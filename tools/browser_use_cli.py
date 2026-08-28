"""Use the Browser Use CLI 3.0 (https://browser-use.com) for browser automation

When browser.backend is "browser-use", the model gets ``browser_exec`` tool
instead of default browser tools
"""

import contextlib
import hashlib
import importlib
import json
import logging
import os
import re
import shutil
import signal
import socket
import subprocess
import tempfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from hermes_constants import get_hermes_home
from utils import is_truthy_value

logger = logging.getLogger(__name__)

_BACKEND_KEY = "browser-use"
BACKEND_DISABLED = "off"

# Cloud daemon names become the BU_NAME env var
_SESSION_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$")

# Set on the env dict by the CDP resolvers when the resolved browser is EXCLUSIVE to this named session
# (per-name provider / named BU cloud / Lightpanda). Popped before the subprocess launches — never exported.
_PRIVATE_BROWSER_SENTINEL = "_HERMES_BU_PRIVATE_BROWSER"

# Prepended to the model's code for logical sessions on a SHARED physical daemon (a /browser connect CDP
# override, or the per-conversation transport below): the daemon attaches to the first existing page at
# startup, and another logical session may have changed its current tab since. Each call therefore reselects
# this logical session's own tab (slot file keyed by HERMES_BU_LOGICAL_SESSION under the harness runtime dir),
# creating a fresh target only when the recorded one is gone.
_OWN_TAB_PREAMBLE = """\
# hermes: select this logical session's tab on the shared CDP transport
def _hermes_ensure_own_tab():
    import hashlib as _hashlib, json as _json, os as _os, tempfile as _tf
    _name = _os.environ.get("HERMES_BU_LOGICAL_SESSION") or _os.environ.get("BU_NAME", "default")
    _runtime = _os.environ.get("BH_RUNTIME_DIR") or _tf.gettempdir()
    _slot = _os.path.join(_runtime, "hermes-tab-%s.json" % _hashlib.sha256(_name.encode()).hexdigest()[:20])
    _tid = None
    try:
        with open(_slot, "r", encoding="utf-8") as _fh:
            _tid = _json.load(_fh).get("target_id")
    except Exception:
        pass
    try:
        _live = {t.get("targetId") for t in cdp("Target.getTargets").get("targetInfos", []) if t.get("type") == "page"}
    except Exception:
        _live = set()
    if _tid not in _live:
        try:
            # Force a fresh target: new_tab() would REUSE a blank current tab,
            # which is exactly the tab a sibling session may also hold.
            _tid = cdp("Target.createTarget", url="about:blank").get("targetId")
        except Exception:
            _tid = None
        if _tid:
            try:
                _os.makedirs(_runtime, mode=0o700, exist_ok=True)
                _fd, _tmp = _tf.mkstemp(prefix=".hermes-tab-", dir=_runtime)
                with _os.fdopen(_fd, "w", encoding="utf-8") as _fh:
                    _json.dump({"target_id": _tid}, _fh)
                _os.replace(_tmp, _slot)
            except OSError:
                pass
    if _tid:
        try:
            switch_tab(_tid)
        except Exception:
            pass  # best-effort: worst case is pre-fix behavior
_hermes_ensure_own_tab()
del _hermes_ensure_own_tab
"""

_DEFAULT_TIMEOUT_S = 300
_MIN_TIMEOUT_S = 5
_MAX_TIMEOUT_S = 1800
_MAX_LEASE_MINUTES = 120
_STDERR_CAP_CHARS = 4000

_TASK_ID_SAFE_RE = re.compile(r"[^A-Za-z0-9._-]+")  # filesystem-safe task ids
# Screenshot paths printed by capture_screenshot(): POSIX or Windows drive-letter absolute.
_IMAGE_PATH_RE = re.compile(r"((?:[A-Za-z]:[\\/]|/)[^\s\"']+?\.(?:png|jpe?g|webp))", re.IGNORECASE)
# http(s) URL literals in exec code checked against browser_navigate's policy
_URL_RE = re.compile(r"https?://[^\s'\"\\)]+", re.IGNORECASE)
_FHS_BIN_DIRS = ("/usr/local/sbin", "/usr/local/bin", "/usr/sbin", "/usr/bin", "/sbin", "/bin")

try:
    import fcntl as _fcntl
except ImportError:  # pragma: no cover - Windows
    _fcntl = None

try:
    import msvcrt as _msvcrt
except ImportError:  # pragma: no cover - POSIX
    _msvcrt = None


# ---------------------------------------------------------------------------
# Per-conversation desktop CDP transport: one browser-harness daemon per (profile, conversation lineage,
# endpoint) so a shared desktop Chrome is attached ONCE per conversation instead of per tool call
# (each fresh attach re-prompts Chrome's "Allow remote debugging?"). Logical sessions (BU_NAME) multiplex it.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _SessionTransport:
    key: str
    runtime_dir: Path
    tmp_dir: Path
    thread_lock: threading.RLock


_TRANSPORT_LOCK_GUARD = threading.Lock()
_TRANSPORT_THREAD_LOCKS: Dict[str, threading.RLock] = {}


def _private_dir(path: Path) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    with contextlib.suppress(OSError):
        path.chmod(0o700)
    return path


def _configure_session_transport(env: dict, *, conversation_id: str, logical_session: str,
                                 private_browser: bool) -> Optional[_SessionTransport]:
    """One browser-harness daemon per profile, conversation lineage, endpoint (exported via BH_RUNTIME_DIR /
    BH_TMP_DIR / HERMES_BU_LOGICAL_SESSION). ``None`` without a lineage scope or for private browsers."""
    scope = str(conversation_id or "").strip()
    if not scope or private_browser:
        return None
    try:
        home = Path(get_hermes_home()).expanduser().resolve()
    except Exception:
        return None
    endpoint = str(env.get("BU_CDP_URL") or env.get("BU_CDP_WS") or "local-auto")
    key = hashlib.sha256(f"{home}\0{scope}\0{endpoint}".encode()).hexdigest()[:24]
    tmp_dir = _private_dir(home / "cache" / "bu" / key / "tmp")
    if os.name == "nt":
        runtime_dir = _private_dir(home / "cache" / "bu" / key / "run")
    else:
        uid = os.getuid() if hasattr(os, "getuid") else 0
        runtime_dir = _private_dir(Path(tempfile.gettempdir()) / f"hermes-bu-{uid}" / key)
        if len(os.fsencode(str(runtime_dir / "bu.sock"))) >= 100:  # AF_UNIX sun_path limit (macOS 104)
            runtime_dir = _private_dir(Path("/tmp") / f"hermes-bu-{uid}" / key)
    env["BH_RUNTIME_DIR"] = str(runtime_dir)
    env["BH_TMP_DIR"] = str(tmp_dir)
    env["HERMES_BU_LOGICAL_SESSION"] = str(logical_session or "default")
    with _TRANSPORT_LOCK_GUARD:
        lock = _TRANSPORT_THREAD_LOCKS.setdefault(key, threading.RLock())
    return _SessionTransport(key, runtime_dir, tmp_dir, lock)


class _TransportExecutionLock:
    """Thread + cross-process lock for one daemon's mutable current target."""

    def __init__(self, transport: _SessionTransport, timeout_s: float):
        self.transport = transport
        self.timeout_s = max(0.1, float(timeout_s))
        self.handle = None
        self.thread_held = False

    def _wait_locked(self, try_lock: Callable[[], None], busy: type, deadline: float) -> None:
        while True:
            try:
                try_lock()
                return
            except busy:
                if time.monotonic() >= deadline:
                    raise TimeoutError("another process owns this browser CDP transport")
                time.sleep(0.05)

    def acquire(self) -> None:
        deadline = time.monotonic() + self.timeout_s
        if not self.transport.thread_lock.acquire(timeout=self.timeout_s):
            raise TimeoutError("another browser_exec call owns this CDP transport")
        self.thread_held = True
        try:
            path = self.transport.runtime_dir / "exec.lock"
            self.handle = open(path, "a+b")
            with contextlib.suppress(OSError):
                os.chmod(path, 0o600)
            if _fcntl is not None:
                self._wait_locked(lambda: _fcntl.flock(self.handle.fileno(), _fcntl.LOCK_EX | _fcntl.LOCK_NB),
                                  BlockingIOError, deadline)
            elif _msvcrt is not None:  # pragma: no cover - Windows
                self.handle.seek(0)
                if self.handle.read(1) == b"":
                    self.handle.write(b"0")
                    self.handle.flush()

                def _try_lock():
                    self.handle.seek(0)
                    getattr(_msvcrt, "locking")(self.handle.fileno(), getattr(_msvcrt, "LK_NBLCK"), 1)
                self._wait_locked(_try_lock, OSError, deadline)
        except Exception:
            self.release()
            raise

    def release(self) -> None:
        if self.handle is not None:
            with contextlib.suppress(OSError):
                if _fcntl is not None:
                    _fcntl.flock(self.handle.fileno(), _fcntl.LOCK_UN)
                elif _msvcrt is not None:  # pragma: no cover - Windows
                    self.handle.seek(0)
                    getattr(_msvcrt, "locking")(self.handle.fileno(), getattr(_msvcrt, "LK_UNLCK"), 1)
            with contextlib.suppress(OSError):
                self.handle.close()
            self.handle = None
        if self.thread_held:
            self.thread_held = False
            self.transport.thread_lock.release()


def _probe_daemon_pid(runtime_dir: Path) -> Optional[int]:
    """Return the live harness daemon PID after an authenticated IPC ping (``bu.sock`` / ``bu.port``)."""
    connection: Optional[socket.socket] = None
    try:
        request: Dict[str, Any] = {"meta": "ping"}
        if os.name == "nt":
            payload = json.loads((runtime_dir / "bu.port").read_text(encoding="utf-8"))
            port, token = int(payload["port"]), str(payload["token"])
            if not token:
                return None
            request["token"] = token
            connection = socket.create_connection(("127.0.0.1", port), timeout=1.0)
        else:
            connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            connection.settimeout(1.0)
            connection.connect(str(runtime_dir / "bu.sock"))
        connection.sendall((json.dumps(request) + "\n").encode("utf-8"))
        raw = b""
        while not raw.endswith(b"\n") and len(raw) <= 65536:
            chunk = connection.recv(65536)
            if not chunk:
                break
            raw += chunk
        response = json.loads(raw or b"{}")
        if not isinstance(response, dict) or response.get("pong") is not True:
            return None
        pid = response.get("pid")
        return pid if type(pid) is int and 0 < pid < (1 << 31) else None
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError):
        return None
    finally:
        if connection is not None:
            with contextlib.suppress(OSError):
                connection.close()


def _daemon_identity(runtime_dir: Path) -> Optional[str]:
    """Content-free identity of the live daemon (``bu.pid`` must match a live ping), or None."""
    try:
        path = runtime_dir / "bu.pid"
        recorded_pid = int(path.read_text(encoding="utf-8").strip())
        live_pid = _probe_daemon_pid(runtime_dir)
        if live_pid is None or live_pid != recorded_pid:
            return None
        return hashlib.sha256(f"{live_pid}:{path.stat().st_mtime_ns}".encode()).hexdigest()[:20]
    except (OSError, ValueError):
        return None


def _record_transport_outcome(transport: _SessionTransport, before: Optional[str], after: Optional[str],
                              logical_session: str, success: bool, error_text: str) -> Dict[str, Any]:
    """Local content-free attach telemetry; never records endpoint or raw IDs."""
    path = transport.tmp_dir / "transport-telemetry.json"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("schema_version") != 1:
            raise ValueError("old schema")
    except (OSError, ValueError, AttributeError):
        data = {"schema_version": 1, "attach_attempts": 0, "attach_successes": 0, "reuses": 0, "drops": 0,
                "events": []}
    attached = reused = False
    event, reason = "unknown", ""
    lowered_error = error_text.lower()
    permission_failed = "permission-blocked" in lowered_error or "allow remote debugging" in lowered_error
    if before and after == before:
        data["reuses"] += 1
        reused, event = True, "reuse"
    elif after and after != before:
        data["attach_attempts"] += 1
        data["attach_successes"] += 1
        attached, event = True, "attach_success"
        reason = "cold_start" if before is None else "daemon_replaced"
        if before is not None:
            data["drops"] += 1
    elif permission_failed:
        data["attach_attempts"] += 1
        attached, event, reason = True, "attach_failed", "permission_blocked"
        if before is not None:
            data["drops"] += 1
    elif before and after is None:
        data["drops"] += 1
        event, reason = "drop_detected", "daemon_exited"
    events = data.get("events", [])
    events.append({"at_unix_ms": int(time.time() * 1000), "event": event, "reason": reason,
                   "outcome": "success" if success else "error"})
    data["events"] = events[-100:]
    data["logical_session_hash"] = hashlib.sha256((logical_session or "default").encode()).hexdigest()[:16]
    temp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        temp.write_text(json.dumps(data, sort_keys=True), encoding="utf-8")
        os.replace(temp, path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temp.unlink()
    return {
        "scope": "conversation_lineage", "transport_key": transport.key,
        "attach_count": data["attach_attempts"], "attach_success_count": data["attach_successes"],
        "attached_this_call": 1 if attached else 0, "reuse_count": data["reuses"], "reused": reused,
        "drop_count": data["drops"],
    }


def _quiet(fn: Callable[[], Any], default: Any, log_prefix: str = "") -> Any:
    """``fn()``, or ``default`` on any exception (debug-logged when ``log_prefix`` is set)."""
    try:
        return fn()
    except Exception as e:
        if log_prefix:
            logger.debug("%s: %s", log_prefix, e)
    return default


def _lazy_call(module: str, name: str, default: Any, log_prefix: str) -> Any:
    """Call ``module.name()`` resolved at call time (tests stub the module / patch the
    attribute); on any failure log ``log_prefix`` and return ``default``."""
    return _quiet(lambda: getattr(importlib.import_module(module), name)(), default, log_prefix)


def _camofox_active(context: str = "") -> bool:
    return _lazy_call("tools.browser_camofox", "is_camofox_mode", False, f"Camofox activity check failed{context}")


def _real_profile_consented() -> bool:
    return _lazy_call("tools.browser_tool_cloud", "_use_real_profile", False, "real-profile consent lookup failed")


def _set_cdp_env(env: dict, cdp: str) -> None:
    """Export a CDP endpoint under the BU_CDP_* contract (http(s) → URL, else WS)."""
    env["BU_CDP_URL" if cdp.startswith(("http://", "https://")) else "BU_CDP_WS"] = cdp


def _has_cdp_env(env: dict) -> bool:
    return bool(env.get("BU_CDP_WS") or env.get("BU_CDP_URL"))


def _export_session_cdp(env: dict, get_session_info: Callable[[str], Any], cache_key: str,
                        fail_msg: Callable[[Exception], str], no_cdp_msg: str) -> Optional[str]:
    """Export the CDP endpoint from ``get_session_info(cache_key)``; error string on failure / no CDP."""
    try:
        cdp = str((get_session_info(cache_key) or {}).get("cdp_url") or "")
    except Exception as e:
        return fail_msg(e)
    if not cdp:
        return no_cdp_msg
    _set_cdp_env(env, cdp)
    return None


def _blocked_url_in_code(code: str) -> Optional[str]:
    """Return an error if a URL literal fails the built-in navigation checks."""
    from tools.browser_tool import evaluate_url_safety
    return next((err.get("error", "Blocked: unsafe URL") for err in map(evaluate_url_safety, _URL_RE.findall(code or "")) if err), None)


def _base_subprocess_env() -> dict:
    from tools.browser_tool import _build_browser_env
    env = _build_browser_env()
    # The CLI runs under its own Python (uv tool / uvx); an inherited PYTHONPATH/PYTHONHOME
    # (Hermes's venv) wins over its site-packages → wrong-ABI C-extensions and a crash.
    # PYTHONPATH/PYTHONHOME inherited from the agent process point at Hermes's venv site-packages, and a
    # child interpreter honors them ahead of its own site-packages — so the CLI imports compiled
    # C-extensions (e.g. pydantic_core) built for the wrong interpreter and crashes on ABI mismatch (#83427,
    # #84841, #86006, #86104). Strip both — the CLI manages its own environment and never needs Hermes's
    # import path.
    env.pop("PYTHONPATH", None)
    env.pop("PYTHONHOME", None)
    env["PATH"] = _floor_subprocess_path(env.get("PATH", ""))
    env.setdefault("ANONYMIZED_TELEMETRY", "false")
    return env


def _floor_subprocess_path(path: str) -> str:
    """Guarantee core system dirs on the CLI subprocess PATH: profile workers (kanban bots, cron) can inherit
    a PATH of only version-manager dirs, and the uv binary's POSIX sh trampoline resolves ``dirname``/``realpath``
    via PATH (exit 127 without /usr/bin). Reuses browser_tool's ``_merge_browser_path`` floor, else appends
    FHS bin dirs. Windows .cmd shims don't trampoline: no-op there."""
    if os.name == "nt":
        return path
    with contextlib.suppress(Exception):
        from tools.browser_tool_install import _merge_browser_path
        return _merge_browser_path(path or "")
    parts = [p for p in (path or "").split(os.pathsep) if p]
    return os.pathsep.join(parts + [d for d in _FHS_BIN_DIRS if d not in set(parts) and os.path.isdir(d)])


def _read_browser_cfg() -> dict:
    """Return the ``browser:`` config section, or {} on any failure."""
    try:
        from hermes_cli.config import cfg_get, read_raw_config
        cfg = cfg_get(read_raw_config(), "browser", default={})
        return cfg if isinstance(cfg, dict) else {}
    except Exception as e:
        logger.debug("Could not read browser config section: %s", e)
        return {}


def _use_gateway(browser_cfg: dict) -> bool:
    return is_truthy_value(browser_cfg.get("use_gateway"), default=False)


def _resource_hygiene_enabled() -> bool:
    """Compatibility shim; browser_tool owns tab-lifecycle configuration."""
    return _lazy_call("tools.browser_tool", "_tab_lifecycle_enabled", False, "tab lifecycle config lookup failed")


def get_browser_backend() -> str:
    """Configured browser backend key ("" = unset → default). YAML 1.1 parses an
    unquoted ``off`` as False — that must mean BACKEND_DISABLED, not "unset"."""
    raw = _read_browser_cfg().get("backend")
    return (BACKEND_DISABLED if raw is False else "") if isinstance(raw, bool) else str(raw or "").strip().lower()


def is_legacy_browser_use_cloud_config(browser_cfg: dict) -> bool:
    """True for pre-CLI direct-API Browser Use cloud configs. An explicit backend or
    a non-Browser-Use cloud_provider wins; Camofox is selected via env var, not
    cloud_provider, so a Camofox user with a stray BROWSER_USE_API_KEY keeps it."""
    if not isinstance(browser_cfg, dict) or browser_cfg.get("backend"):
        return False
    provider = str(browser_cfg.get("cloud_provider") or "").strip().lower()
    if provider not in {"browser-use", ""} or _use_gateway(browser_cfg) or _camofox_active(" during migration"):
        return False
    return bool(os.getenv("BROWSER_USE_API_KEY"))


def is_browser_use_cli_mode() -> bool:
    """True when the Browser Use CLI replaces the built-in browser stack. Browser Use mode is the DEFAULT:
    unset ``browser.backend`` ("") enables it whenever the CLI is runnable (installed binary or uvx);
    ``browser.backend: off`` keeps the built-in browser_* tools. Camofox always falls back to the built-in
    tools (Firefox, custom HTTP API, no CDP surface for the harness)."""
    if _camofox_active():
        return False
    backend = get_browser_backend()
    return backend == _BACKEND_KEY if backend else (is_legacy_browser_use_cloud_config(_read_browser_cfg()) or _find_cli() is not None)


def default_downgrade_notice() -> Optional[str]:
    """One-line notice when ``browser.backend`` is unset but the CLI is not runnable, so
    the session fell back to the built-in tools. Rate-limited to once per 24h via a stamp file."""
    try:
        if get_browser_backend() or _camofox_active() or _find_cli() is not None:
            return None  # explicit choice / Camofox / CLI present — nothing downgraded
        stamp = Path(get_hermes_home()) / "cache" / ".browser_use_default_notice"
        with contextlib.suppress(OSError):
            if 0 <= time.time() - stamp.stat().st_mtime < 24 * 3600:
                return None
        with contextlib.suppress(OSError):
            stamp.parent.mkdir(parents=True, exist_ok=True)
            stamp.touch()
        return ("Browser Use CLI not found — using the built-in browser tools. Run `hermes tools` "
                "(Browser Automation → Browser Use) to install it, or `browser.backend: off` in config.yaml to silence this.")
    except Exception as e:  # pragma: no cover — a notice must never break startup
        logger.debug("browser-use downgrade notice failed: %s", e)
        return None


def _managed_bin_dir() -> str:
    """$HERMES_HOME/bin — where install.sh puts uv/uvx and install_cli() links browser-use."""
    return str(Path(get_hermes_home()) / "bin")


def _find_cli() -> Optional[List[str]]:
    """Locate the browser-use CLI, or None when it can't be run. MANAGED-FIRST: Hermes' own ``$HERMES_HOME/bin``
    copy always wins so every session drives one Hermes-controlled binary; PATH and the user-level tool dir
    (~/.local/bin, or uv's %APPDATA%/uv/bin on Windows — Desktop/TUI workers may start with a minimal PATH
    that omits it) are fallbacks; uvx zero-install (same probe order) is last."""
    if os.name == "nt":
        appdata = os.environ.get("APPDATA")
        user_bin = str(Path(appdata) / "uv" / "bin") if appdata else None
    else:
        user_bin = str(Path(os.path.expanduser("~")) / ".local" / "bin")
    probe_paths = [p for p in (_managed_bin_dir(), None, user_bin) if p is None or p]  # None = PATH
    for name, argv in (("browser-use", lambda b: [b]), ("uvx", lambda b: [b, "browser-use"])):
        for probe_path in probe_paths:
            found = shutil.which(name, path=probe_path)
            if found:
                return argv(found)
    return None


def install_cli(timeout_s: int = 600) -> Tuple[bool, str]:
    """Install the browser-use CLI via ``uv tool install`` (managed uv via ``ensure_uv`` → uv on PATH), linking
    the binary into ``$HERMES_HOME/bin`` (``UV_TOOL_BIN_DIR``) so ``_find_cli()`` resolves it for every profile.
    Returns ``(ok, message)``; never raises. MANAGED-FIRST: only the managed copy short-circuits — a browser-use
    on PATH is a user-level side install and must not block provisioning the canonical copy (version drift)."""
    bin_dir = _managed_bin_dir()
    managed = shutil.which("browser-use", path=bin_dir)
    if managed:
        return True, f"browser-use CLI already installed ({managed})"

    def _managed_uv() -> Optional[str]:
        from hermes_cli.managed_uv import ensure_uv
        return str(ensure_uv() or "") or None
    uv_bin = _quiet(_managed_uv, None, "Managed uv bootstrap unavailable") or shutil.which("uv")
    if not uv_bin:
        return False, ("uv is not available and could not be bootstrapped. Install uv "
                       "(https://docs.astral.sh/uv/) and run `uv tool install browser-use`.")
    env = {**os.environ, "UV_NO_CONFIG": "1"}
    try:
        Path(bin_dir).mkdir(parents=True, exist_ok=True)
        env["UV_TOOL_BIN_DIR"] = bin_dir
    except OSError as e:
        logger.debug("Could not prepare %s: %s", bin_dir, e)

    try:
        result = subprocess.run([uv_bin, "tool", "install", "browser-use"], capture_output=True, text=True, encoding="utf-8",
                                errors="replace", env=env, timeout=timeout_s, stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        return False, f"`uv tool install browser-use` timed out after {timeout_s}s"
    except Exception as e:
        return False, f"Failed to run `uv tool install browser-use`: {e}"

    if result.returncode != 0:
        tail = "\n".join((result.stderr or result.stdout or "").strip().splitlines()[-3:])
        return False, f"`uv tool install browser-use` failed:\n{tail}"
    found = _find_cli()
    if not found or len(found) != 1:
        return False, ("install reported success but the browser-use binary is still not resolvable — "
                       "run `uv tool install browser-use` manually")
    return True, f"browser-use CLI installed ({found[0]})"


def _workspace_dir(task_id: Optional[str]) -> Optional[str]:
    """Stable per-task scratch dir that persists across browser_exec calls"""
    if os.environ.get("BH_AGENT_WORKSPACE"):
        return os.environ["BH_AGENT_WORKSPACE"]
    try:
        safe = _TASK_ID_SAFE_RE.sub("_", str(task_id or "default"))[:80] or "default"
        path = Path(get_hermes_home()) / "cache" / "browser-use" / "workspace" / safe
        path.mkdir(parents=True, exist_ok=True)
        return str(path)
    except Exception as e:
        logger.debug("browser_exec workspace unavailable: %s", e)
        return None


def _find_screenshot(stdout: str, since: float) -> Optional[str]:
    """Last screenshot path printed during this exec that exists and was written after
    the exec started, or None."""
    for path in reversed(_IMAGE_PATH_RE.findall(stdout or "")):
        try:
            if os.path.isfile(path) and os.path.getmtime(path) >= since - 1:
                return path
        except OSError:
            continue
    return None


def _native_screenshot_result(result: Dict[str, Any], path: str) -> Optional[Dict[str, Any]]:
    """Build a multimodal tool result attaching path for vision models"""
    try:
        from tools.vision_tools import (_EMBED_MAX_DIMENSION, _EMBED_TARGET_BYTES,
                                        _resize_image_for_vision, _should_use_native_vision_fast_path)
        if not _should_use_native_vision_fast_path():
            return None
        # History-reuse cap: this data URL bakes into the tool result and is re-sent every later turn —
        # same policy as the vision_analyze / browser_vision native embeds.
        data_url = _resize_image_for_vision(Path(path), mime_type="image/png", max_base64_bytes=_EMBED_TARGET_BYTES,
                                            max_dimension=_EMBED_MAX_DIMENSION, force_jpeg=True)
        text = json.dumps(result, ensure_ascii=False)
        attached = text + "\n\nThe screenshot from this call is attached — inspect it with your native vision."
        return {"_multimodal": True, "text_summary": text, "meta": {"screenshot_path": path, "native_vision": True},
                "content": [{"type": "text", "text": attached}, {"type": "image_url", "image_url": {"url": data_url}}]}
    except Exception as e:
        logger.debug("Native screenshot attach failed (falling back to text): %s", e)
        return None


def _backend_cache_key(task_id: Optional[str], session_name: str = "") -> str:
    """Session-cache key for a backend browser: named sessions get their own."""
    return f"bu-named-{session_name}" if session_name else (task_id or "browser-exec-default")


def _resolve_lightpanda_cdp(env: dict, task_id: Optional[str], session_name: str = "") -> Optional[str]:
    """Point the harness at a Hermes-spawned ``lightpanda serve`` (``browser.engine: lightpanda`` and
    nothing of higher precedence claimed the session). Each cache key gets its own process via the
    legacy ``_get_session_info()`` (cache, reaper, atexit): private browser, own-tab preamble skipped."""
    try:
        from tools.browser_tool_session import _get_session_info
        from tools.browser_tool_lightpanda_fallback import _using_lightpanda_engine
        if not _using_lightpanda_engine():
            return None
    except Exception as e:  # stubbed browser_tool in tests / engine lookup failure
        logger.debug("browser engine lookup failed: %s", e)
        return None
    err = _export_session_cdp(
        env, _get_session_info, _backend_cache_key(task_id, session_name),
        lambda e: (f"Lightpanda could not be started: {e} Set browser.engine to auto "
                   "to use local Chrome, or switch backends via `hermes tools` → Browser Automation."),
        "Lightpanda session returned no CDP endpoint. Set browser.engine to auto to use local Chrome.",
    )
    if err is None:
        env[_PRIVATE_BROWSER_SENTINEL] = "1"
    return err


def _resolve_managed_chromium_cdp(env: dict, task_id: Optional[str], session_name: str = "") -> Optional[str]:
    """Point the harness at Hermes' packaged Chromium, launched through agent-browser for this cache key —
    the same browser the built-in tools drive. Left alone, the harness discovers the user's INSTALLED
    Chrome on its default profile, which needs the chrome://inspect toggle + an Allow popup per run and
    is blocked outright on Chrome >=136; on a headless box it just reports ``chrome-not-running``.
    ``get cdp-url`` runs through ``_run_browser_command`` (legacy cache, inactivity reaper, atexit, Chromium
    preflight/auto-install) on EVERY call: it launches the browser cold, follows a relaunch, and refreshes
    the agent-browser daemon's idle timer, which never sees the harness's direct CDP traffic."""
    try:
        from tools.browser_tool_session import _run_browser_command
        from tools.browser_tool import _get_open_command_timeout
    except Exception as e:  # pragma: no cover — stubbed browser_tool in tests
        logger.debug("managed chromium resolution unavailable: %s", e)
        return None
    res = _run_browser_command(_backend_cache_key(task_id, session_name), "get", ["cdp-url"],
                               timeout=_get_open_command_timeout(first_open=True))
    cdp = str(((res or {}).get("data") or {}).get("cdpUrl") or "") if (res or {}).get("success") else ""
    if not cdp:
        return (f"The local browser could not be started: {(res or {}).get('error') or 'agent-browser returned no CDP endpoint'} "
                "Run `hermes tools` → Browser Automation to (re)install Chromium, or switch backends.")
    _set_cdp_env(env, cdp)
    env[_PRIVATE_BROWSER_SENTINEL] = "1"  # one Chromium per cache key: nothing to share a tab with
    return None


def _resolve_local_engine_cdp(env: dict, task_id: Optional[str], session_name: str = "") -> Optional[str]:
    """Local engine (no provider / override): ``browser.engine: lightpanda`` or the packaged Chromium."""
    err = _resolve_lightpanda_cdp(env, task_id, session_name)
    if err or _has_cdp_env(env):
        return err
    return _resolve_managed_chromium_cdp(env, task_id, session_name)


def _resolve_backend_cdp(env: dict, task_id: Optional[str], session_name: str = "") -> Optional[str]:
    """Point the harness at the configured backend's CDP endpoint; error string on failure.

    Precedence: (1) ``BU_CDP_WS``/``BU_CDP_URL`` already in env (operator override); (2) ``BROWSER_CDP_URL``
    env / ``browser.cdp_url`` (``/browser connect``); (3) a cloud provider via the legacy ``_get_session_info()``
    so browser_exec shares the SAME session machinery (per-task cache, expiry, reaper, atexit);
    (4) the local engine — ``browser.engine: lightpanda`` or Hermes' packaged Chromium via agent-browser
    (never the harness's own discovery of the user's installed Chrome); (5) BU direct-API configs → None:
    the CLI reaches BU cloud natively (BU_AUTOSPAWN). ``session_name`` (BU_NAME) keys the session cache so
    each name gets its OWN browser — what makes named sessions concurrent-safe.
    """
    if _has_cdp_env(env):
        return None
    try:
        from tools.browser_tool_cloud import _get_cloud_provider
        from tools.browser_tool_session import _get_session_info
        from tools.browser_tool_cdp import _get_cdp_override
    except Exception as e:  # pragma: no cover — stubbed browser_tool in tests
        logger.debug("browser_tool backend resolution unavailable: %s", e)
        return None
    override = _quiet(_get_cdp_override, "")
    if override:
        _set_cdp_env(env, override)
        return None
    provider = _quiet(_get_cloud_provider, None, "Cloud provider lookup failed")
    if provider is None:
        return _resolve_local_engine_cdp(env, task_id, session_name)

    # Browser Use direct-API configs: the CLI talks to BU cloud natively (BU_AUTOSPAWN / auth login) — the
    # legacy provider would create a second, redundant session. The Nous-gateway variant (use_gateway: true)
    # DOES resolve through the provider: the gateway provisions the browser server-side and returns its CDP URL.
    provider_key = str(getattr(provider, "name", "") or "").strip().lower()
    if provider_key == _BACKEND_KEY and not _use_gateway(_read_browser_cfg()):
        env[_PRIVATE_BROWSER_SENTINEL] = "1"  # named BU cloud browsers are exclusive to their daemon
        return None

    provider_name = type(provider).__name__
    err = _export_session_cdp(
        env, _get_session_info, _backend_cache_key(task_id, session_name),
        lambda e: (f"Cloud browser provider {provider_name} failed to provide a session: {e}. "
                   "Fix the provider configuration or switch backends via `hermes tools` → Browser Automation."),
        f"Cloud browser provider {provider_name} returned no CDP endpoint, so Browser Use mode "
        "cannot drive it. Switch to the built-in browser tools for this provider.",
    )
    # A provider browser keyed bu-named-<name> is exclusive to this session — the
    # own-tab preamble would just leak a blank tab into it.
    if err is None and session_name:
        env[_PRIVATE_BROWSER_SENTINEL] = "1"
    return err


def _resolve_real_profile_cdp(env: dict, force_local: bool) -> Optional[str]:
    """Point the harness at the user's real-profile copy-browser (a SNAPSHOT of their default Chromium
    profile, hermes_cli.browser_connect) when consented. Two ways in: the effective backend is already local
    (no provider, CDP override, or legacy BU cloud config) → silent upgrade; or ``force_local`` (consent-gated
    ``local`` arg) → the user's browser even under a cloud backend. Operator overrides (BU_CDP_* env,
    /browser connect, ``browser.cdp_url``) own the session either way. Fail closed: a launch error is
    returned so a consented user is never silently downgraded."""
    if not _real_profile_consented() or _has_cdp_env(env):
        return None
    try:
        from tools.browser_tool_cdp import _get_cdp_override_raw
        from tools.browser_tool_cloud import _get_cloud_provider
        from tools.browser_tool_real_profile import _real_profile_cdp
    except Exception as e:  # pragma: no cover — stubbed browser_tool in tests
        logger.debug("real-profile backend resolution unavailable: %s", e)
        return None
    if _quiet(_get_cdp_override_raw, ""):
        return None
    # Only auto-upgrade genuinely-local attaches; any cloud path (provider, provider lookup failure, or
    # legacy BU cloud config) stays on its backend unless the model passes local=true.
    if not force_local and (_quiet(_get_cloud_provider, object()) is not None
                            or is_legacy_browser_use_cloud_config(_read_browser_cfg())):
        return None
    cdp, err = _real_profile_cdp()
    if cdp and not err:
        _set_cdp_env(env, cdp)
    return err or None


def _attach_vault_supervisor(env: dict, task_id: Optional[str]) -> None:
    """Attach the per-task CDP supervisor to the browser this exec drives so ``browser_vault_fill`` has
    a secret-capable WebSocket (never argv) into the SAME browser. Only CDP-routed backends expose an
    endpoint; BU direct-cloud (BU_AUTOSPAWN) does not, and the vault tools report ``supervisor_required``."""
    cdp = env.get("BU_CDP_WS") or env.get("BU_CDP_URL")
    if not cdp:
        return
    try:
        from tools.browser_supervisor import SUPERVISOR_REGISTRY
        from tools.browser_tool_cdp import _get_dialog_policy_config, _resolve_cdp_override
        policy, timeout_s = _get_dialog_policy_config()
        SUPERVISOR_REGISTRY.get_or_start(task_id=task_id or "default", cdp_url=_resolve_cdp_override(cdp),
                                         dialog_policy=policy, dialog_timeout_s=timeout_s)
    except Exception as exc:
        logger.debug("browser_exec: CDP supervisor attach failed (non-fatal): %s", exc)


def _route_backend(env: dict, session: str, task_id: Optional[str], local: bool) -> Optional[str]:
    """Resolve where the harness connects; returns an error string or None. Real-profile consent runs
    BEFORE provider resolution so a hit short-circuits the cloud path via the BU_CDP_* env contract. Named
    sessions compose with the backend: BU_NAME namespaces the harness daemon (IPC socket, log, pid) and on
    provider backends additionally keys its own cloud browser."""
    rp_err = _resolve_real_profile_cdp(env, force_local=local)
    if rp_err:
        return rp_err
    # local=True is only served by the real-profile route; consent off must not pretend.
    if local and not _has_cdp_env(env) and not _real_profile_consented():
        return ("local=true was requested but browser.use_real_profile is off. Enable it in config.yaml "
                "(browser.use_real_profile: true) or the desktop Settings → Browser section, then retry.")
    return _resolve_backend_cdp(env, task_id, session_name=session)


def _group_popen_kwargs() -> dict:
    """Popen kwargs starting the CLI in its own process group (a new session on POSIX) so a
    timeout can take down every process that inherited the capture pipes, not just the CLI
    child. Windows also hides the console the .cmd shim would flash (as browser_tool does)."""
    def _flags() -> dict:
        from hermes_cli._subprocess_compat import windows_hide_flags
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        return {"creationflags": windows_hide_flags() | getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0),
                "startupinfo": si}
    return _quiet(_flags, {}, "Windows hide-flags unavailable") if os.name == "nt" else {"start_new_session": True}


def _clamp_timeout(timeout_s: Any) -> int:
    try:
        return max(_MIN_TIMEOUT_S, min(int(timeout_s), _MAX_TIMEOUT_S))
    except (TypeError, ValueError):
        return _DEFAULT_TIMEOUT_S


# After a whole-group SIGKILL, every pipe holder is dead, so the drain below is normally
# instant; the deadline only guards against a process outside the group still holding a pipe.
_POST_KILL_DRAIN_S = 10.0


def _kill_cli_process_group(proc) -> None:
    """SIGKILL the CLI's whole process group (POSIX; ``start_new_session`` made pgid == pid) or,
    on Windows, its process tree via ``taskkill /T /F`` — the only group-wide kill it offers."""
    if os.name == "nt":
        from hermes_cli._subprocess_compat import windows_hide_flags
        with contextlib.suppress(OSError, subprocess.SubprocessError):
            subprocess.run(["taskkill", "/T", "/F", "/PID", str(proc.pid)], stdin=subprocess.DEVNULL,
                           capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10,
                           check=False, creationflags=windows_hide_flags())
        return
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(proc.pid, signal.SIGKILL)  # windows-footgun: ok — POSIX only, the nt branch returned above


def _run_cli_killing_process_group(cmd, code, env, timeout):
    """Run the CLI in its own process group and kill the whole group on timeout.

    ``subprocess.run`` only kills the direct child on ``TimeoutExpired``; a grandchild that
    inherited the stdout/stderr pipes (browser_harness daemon / Chrome helper) is orphaned
    still holding them, and on Windows ``run()``'s unbounded post-kill ``communicate()`` then
    blocks on pipe EOF forever — so the tool call, plus its activity heartbeat, wedges (#106244).
    """
    proc = subprocess.Popen(
        cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding="utf-8", errors="replace", env=env, **_group_popen_kwargs(),
    )
    try:
        stdout, stderr = proc.communicate(input=code, timeout=timeout)
    except subprocess.TimeoutExpired:
        _kill_cli_process_group(proc)
        with contextlib.suppress(subprocess.TimeoutExpired):
            proc.communicate(timeout=_POST_KILL_DRAIN_S)
        raise
    return subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)


def _validate_lease(lease_minutes: Any, lease_reason: Any) -> Tuple[int, str, Optional[str]]:
    """Validate the bounded tab lease; returns ``(minutes, reason, error)``."""
    try:
        lease = int(lease_minutes or 0)
    except (TypeError, ValueError):
        return 0, "", f"lease_minutes must be an integer from 0 to {_MAX_LEASE_MINUTES}."
    if lease < 0 or lease > _MAX_LEASE_MINUTES:
        return 0, "", f"lease_minutes must be between 0 and {_MAX_LEASE_MINUTES}."
    reason = str(lease_reason or "").strip()
    if lease and not reason:
        return 0, "", ("lease_reason is required when lease_minutes is non-zero. "
                       "Use a short task-specific reason.")
    return lease, reason, None


def browser_exec(code: str, session: str = "", timeout_s: int = _DEFAULT_TIMEOUT_S,
                 lease_minutes: int = 0, lease_reason: str = "",
                 task_id: Optional[str] = None, local: bool = False, turn_id: Optional[str] = None,
                 conversation_id: Optional[str] = None):
    """Run Python code through the browser-use CLI, and return its output"""
    from tools.registry import tool_error, tool_result
    if not code or not code.strip():
        return tool_error("No code provided. Pass Python that uses the pre-imported helpers, e.g. new_tab(\"https://example.com\") then print(page_info()).")

    blocked = _blocked_url_in_code(code)
    if blocked:
        return tool_error(blocked)

    lease, reason, lease_err = _validate_lease(lease_minutes, lease_reason)
    if lease_err:
        return tool_error(lease_err)

    cmd = _find_cli()
    if not cmd:
        return tool_error("browser-use CLI not found on PATH, and uvx is unavailable for a zero-install run. "
                          "Install it with `uv tool install browser-use` (or `pipx install browser-use`), "
                          "then run `browser-use --doctor` to verify the setup.")

    env = _base_subprocess_env()
    if session:
        if not _SESSION_RE.match(session):
            return tool_error(f"Invalid session name {session!r}: use 1-64 letters, digits, "
                              "dashes, or underscores (e.g. 'r7k2').")
        env["BU_NAME"] = session
    route_err = _route_backend(env, session, task_id, bool(local))
    if route_err:
        return tool_error(route_err)
    _attach_vault_supervisor(env, task_id)

    # SHARED browser (/browser connect CDP override): pin each named session to its own tab (see
    # _OWN_TAB_PREAMBLE). Private per-name browsers skip this — nothing to collide with.
    private_browser = env.pop(_PRIVATE_BROWSER_SENTINEL, None)  # always pop: never exported to the CLI
    transport = _configure_session_transport(env, conversation_id=str(conversation_id or ""),
                                             logical_session=session or "default",
                                             private_browser=bool(private_browser))

    workspace = _workspace_dir(task_id)
    if workspace:
        env["BH_AGENT_WORKSPACE"] = workspace

    # BU_AUTOSPAWN makes the CLI start a Browser Use cloud browser when no local
    # Chrome/CDP endpoint is reachable (their API key authenticates it)
    if "BU_AUTOSPAWN" not in env and is_legacy_browser_use_cloud_config(_read_browser_cfg()):
        env["BU_AUTOSPAWN"] = "1"

    timeout = _clamp_timeout(timeout_s)

    # Ownership-aware tab lifecycle (browser.resource_hygiene): on a SHARED loopback CDP browser this
    # conversation owns only the tabs it created/claimed this call and closes only those afterwards.
    hygiene_guard = None
    if _resource_hygiene_enabled() and not private_browser:
        from tools.browser_tool import prepare_browser_tab_lifecycle

        hygiene_guard, hygiene_start_error = prepare_browser_tab_lifecycle(
            session_name=session, owner_key=turn_id or task_id or "browser-exec-default",
            lease_minutes=lease, lease_reason=reason, lock_timeout_s=min(60, timeout),
            cdp_url=str(env.get("BU_CDP_URL") or env.get("BU_CDP_WS") or ""),
            private_browser=bool(private_browser),
        )
        if hygiene_start_error:
            return tool_error("Browser tab lifecycle blocked this call before navigation: "
                              f"{hygiene_start_error}. No browser code was executed.")

    if hygiene_guard is not None and hygiene_guard.target_id:
        code = f"switch_tab({json.dumps(hygiene_guard.target_id)})\n" + code
    elif not private_browser and (session or transport is not None):
        code = _OWN_TAB_PREAMBLE + code

    started = time.time()
    proc = None
    execution_error = None
    hygiene_report = None
    transport_telemetry = None
    before_daemon = None
    execution_lock = _TransportExecutionLock(transport, min(60, timeout)) if transport is not None else None
    lock_held = False
    try:
        if execution_lock is not None and transport is not None:
            execution_lock.acquire()
            lock_held = True
            before_daemon = _daemon_identity(transport.runtime_dir)
        proc = _run_cli_killing_process_group(cmd, code, env, timeout)
    except subprocess.TimeoutExpired:
        execution_error = (f"browser-use exec timed out after {timeout}s. The daemon may still be working; retry "
                           f"with a larger timeout_s (max {_MAX_TIMEOUT_S}), or split the work into several calls that "
                           "append to workspace files — anything already written to the workspace is preserved.")
    except TimeoutError as e:
        execution_error = f"Browser CDP transport is busy: {e}"
    except OSError as e:
        execution_error = f"Failed to launch browser-use CLI: {e}"
    finally:
        try:
            hygiene_report = hygiene_guard.finish() if hygiene_guard is not None else None
        finally:
            if transport is not None and lock_held:
                try:
                    transport_telemetry = _record_transport_outcome(
                        transport, before_daemon, _daemon_identity(transport.runtime_dir), session or "default",
                        execution_error is None and proc is not None and proc.returncode == 0,
                        execution_error or ((proc.stderr or "") if proc is not None else ""),
                    )
                except Exception:
                    logger.debug("browser CDP telemetry failed", exc_info=True)
            if lock_held and execution_lock is not None:
                execution_lock.release()

    if execution_error:
        if hygiene_report and not hygiene_report.get("ok", True):
            execution_error += " Cleanup also failed: " + "; ".join(hygiene_report.get("errors") or ["unknown hygiene error"])
        return tool_error(execution_error)
    assert proc is not None

    result = {"success": proc.returncode == 0, "exit_code": proc.returncode, "output": proc.stdout}
    if workspace:
        result["workspace"] = workspace
    if session:
        result["session"] = session
    if transport_telemetry is not None:
        result["cdp_transport"] = transport_telemetry
    if hygiene_report is not None:
        result["hygiene"] = hygiene_report
        if not hygiene_report.get("ok", False):
            result["success"] = False
    stderr = (proc.stderr or "").strip()
    if len(stderr) > _STDERR_CAP_CHARS:
        stderr = stderr[:_STDERR_CAP_CHARS] + "\n… (stderr truncated)"
    if stderr:
        result["stderr"] = stderr
    screenshot = _find_screenshot(proc.stdout, started)
    if screenshot:
        result["screenshot_path"] = screenshot
        native = _native_screenshot_result(result, screenshot)
        if native is not None:
            return native
    return tool_result(result)


_HEADER_BASE = (
    "Drive a real web browser via the Browser Use CLI: `code` runs as full Python (stdlib available) "
    "with pre-imported browser helpers; stdout comes back in the result. Start `code` with a one-line "
    "comment describing the step for the user in plain language, max 60 chars "
    "(e.g. `# Searching Amazon for paper towels`) — the UI shows it as the step label.\n\n"
    "STATE: the browser session and workspace persist across calls; Python variables do NOT (fresh "
    "interpreter each call). The workspace dir is $BH_AGENT_WORKSPACE (also `workspace` in every result); "
    "functions defined in agent_helpers.py there are auto-imported into every call. For multi-item tasks "
    "('all N products / every entry'), append each batch to a JSON/CSV file in the workspace, then read it "
    "back and aggregate in code — dedupe/count/sort with Python, not in your head — and verify the "
    "collected count against what was asked before answering.\n\n"
    "Batch each sub-procedure (navigate, wait, extract, act) into one call — do not spend a call per "
    "action — but for long extractions prefer several medium calls that append to workspace files over "
    "one giant call, so progress survives timeouts."
)

_HEADER_VISION = (
    " Screenshots are attached to your context automatically: when the exec output contains a "
    "capture_screenshot() path, the image arrives with this tool's result and you inspect it directly "
    "with your own vision — never send browser screenshots to a separate vision tool."
)

_HEADER_TEXT_ONLY = (
    " Your model cannot view images, so work text-first: page_info() for state, js() for "
    "reading/extracting DOM text, fill_input(selector, text) for inputs, and "
    "js(\"document.querySelector('…').click()\") for clicks — skip the screenshot-driven workflow described below."
)

# Appended when the local engine is Lightpanda: no graphical renderer, and one CDP
# connection holds one page — a second Target.createTarget fails with
# TargetAlreadyLoaded (drop the new_tab() sentence once lightpanda-io/browser#1962 lands).
_HEADER_LIGHTPANDA = (
    " The local engine is Lightpanda (no graphical renderer, one page per session): capture_screenshot() "
    "is unavailable, so work text-first; navigate with new_tab(url) exactly once, then goto_url(url) for "
    "every later navigation — a second new_tab() fails with TargetAlreadyLoaded."
)

# Pinned quick-reference for the CLI's pre-imported helpers, replacing the live
# ``browser-use skill`` fetch (uncontrolled third-party text in every schema: version
# drift, supply-chain exposure, byte-unstable prompt). A/B benchmarked ~equal.
_HELPERS_DIGEST = (
    "\n\nHELPERS (pre-imported): new_tab(url) opens/navigates (use for the FIRST navigation), goto_url(url) "
    "navigates the current tab, wait_for_load() after navigation, page_info() summarizes the current page "
    "state, js(expr) evaluates a JS expression and returns its value (js('document.title'); wrap function "
    "bodies as js('(() => {...})()') — a bare '() => {...}' returns the function itself, uncalled), "
    "fill_input(selector, text) types into inputs, click_at_xy(x, y) clicks viewport coordinates, "
    "capture_screenshot() saves and prints a screenshot path, cdp('Domain.method', **kwargs) is raw CDP — "
    "cdp('Accessibility.getFullAXTree')['nodes'] lists every element's role/name/backendDOMNodeId (filter "
    "in Python before printing; it is thousands of nodes), then cdp('DOM.getBoxModel', backendNodeId=n) "
    "gives click coordinates. ensure_real_tab() recovers from a stale/internal tab. Login walls: never guess "
    "credentials; see the vault note below if present, otherwise stop and ask the user."
)


_HEADER_TAB_LIFECYCLE = (
    "\n\nTAB LIFECYCLE: Local tabs created or claimed from a blank baseline close automatically after each "
    "browser_exec call, including errors and timeouts. The tool verifies closure and leaves one blank "
    "baseline page. When the NEXT browser_exec call genuinely must reuse the current tab, set lease_minutes "
    "(1-120) and a task-specific lease_reason. On the final call, omit the lease so owned tabs close. "
    "Never lease a tab merely because it may be useful later."
)


def _description_header() -> str:
    """Header tailored to the active engine, vision, and tab lifecycle."""
    if _lazy_call("tools.browser_tool_lightpanda_fallback", "lightpanda_engine_status", (False, ""),
                  "lightpanda engine status unavailable")[0]:
        # No screenshots, whatever the model sees; Lightpanda sessions are private and one-page-only, so
        # shared-CDP tab lifecycle instructions do not apply even when the feature is enabled.
        return _HEADER_BASE + _HEADER_TEXT_ONLY + _HEADER_LIGHTPANDA
    hygiene = _HEADER_TAB_LIFECYCLE if _resource_hygiene_enabled() else ""
    vision = _lazy_call("tools.vision_tools", "_should_use_native_vision_fast_path", False, "")
    return _HEADER_BASE + hygiene + (_HEADER_VISION if vision else _HEADER_TEXT_ONLY)


def _dynamic_schema_overrides() -> dict:
    overrides: dict = {"description": _description_header() + _HELPERS_DIGEST}
    # ``local`` exists ONLY when the user consented to real-profile browsing — everyone
    # else's schema carries zero extra surface. The caller memoizes on config.yaml mtime,
    # so toggling consent applies next session, not mid-chat.
    if _real_profile_consented():
        props = dict(BROWSER_EXEC_SCHEMA["parameters"]["properties"])
        props["local"] = {
            "type": "boolean", "default": False,
            "description": ("Drive the user's own local browser (a Hermes-managed copy of their real "
                            "default-Chromium profile, logins/cookies included) instead of the configured "
                            "cloud browser backend. Use when the user asks to act as themselves — their "
                            "accounts, their sessions. No-op when the backend is already local. Default false."),
        }
        overrides["parameters"] = {**BROWSER_EXEC_SCHEMA["parameters"], "properties": props}
    return overrides


BROWSER_EXEC_SCHEMA = {
    "name": "browser_exec",
    # Static fallback description, used only when the CLI (and uvx) is unavailable
    "description": (_HEADER_BASE + _HELPERS_DIGEST
                    + "\n\n(The browser-use CLI is not installed yet. Install it with `uv tool install browser-use`.)"),
    "parameters": {
        "type": "object",
        "properties": {
            "code": {"type": "string", "description": "Python code to execute using the pre-imported browser helpers. Use print(...) for any data you need back."},
            "session": {"type": "string",
                        "description": ("Named logical browser session. Related calls reuse its tab namespace; cloud "
                                        "backends may also allocate a browser. Shared local/CDP calls multiplex one "
                                        "persistent physical connection per Hermes conversation lineage, avoiding "
                                        "Chrome re-prompts. Reuse the same name for related calls; omit for default.")},
            "timeout_s": {"type": "integer", "default": _DEFAULT_TIMEOUT_S,
                          "description": f"Max seconds to wait for the code to finish (default {_DEFAULT_TIMEOUT_S}, max {_MAX_TIMEOUT_S})."},
            "lease_minutes": {"type": "integer", "minimum": 0, "maximum": _MAX_LEASE_MINUTES, "default": 0,
                              "description": ("Keep local task-owned tabs for the next call for 1-120 minutes. Default 0 "
                                              "closes them after this call. Requires lease_reason; omit on the final call.")},
            "lease_reason": {"type": "string", "maxLength": 500,
                             "description": ("Short task-specific reason for a non-zero lease. Do not include URLs, "
                                             "credentials, or private page content.")},
        },
        "required": ["code"],
    },
}


# browser_exec is additionally gated at tool-definition time — sessions whose toolsets
# lack ``terminal`` never see it (model_tools._compute_tool_definitions). check_fn only
# answers "is Browser Use mode configured"; surface policy lives with the session.
from tools.registry import registry

registry.register(
    name="browser_exec",
    toolset="browser-use",
    schema=BROWSER_EXEC_SCHEMA,
    handler=lambda args, **kw: browser_exec(
        code=args.get("code", ""), session=args.get("session", "") or "",
        timeout_s=args.get("timeout_s", _DEFAULT_TIMEOUT_S),
        lease_minutes=args.get("lease_minutes", 0), lease_reason=args.get("lease_reason", ""),
        task_id=kw.get("task_id"), local=bool(args.get("local", False)), turn_id=kw.get("turn_id"),
        conversation_id=kw.get("conversation_id") or kw.get("session_id"),
    ),
    check_fn=is_browser_use_cli_mode,
    dynamic_schema_overrides=_dynamic_schema_overrides,
    emoji="🌐",
)
