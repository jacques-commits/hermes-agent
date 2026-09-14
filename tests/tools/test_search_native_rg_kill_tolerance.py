"""Local patch (upstream #104696 / PR #104879): ``_run_rg_native`` must keep a
finished bounded search's results when the process-group kill helper raises
ESRCH/EPERM because rg already exited (macOS) — instead of surfacing
``[Errno 3] No such process`` / ``[Errno 1] Operation not permitted`` as a tool
error and dropping the collected output."""

import sys

import pytest

from tools.environments import local as local_env
from tools.environments.local import LocalEnvironment
from tools.file_operations import ShellFileOperations

pytestmark = pytest.mark.skipif(sys.platform == "win32", reason="native rg lane is POSIX-only")

# Emits 20 lines then stays alive so the bounded read (5 lines) always takes the kill path.
_CHILD_ARGV = ["sh", "-c", "'seq 1 20; exec sleep 30'"]


@pytest.mark.parametrize("exc", [ProcessLookupError(3, "No such process"), PermissionError(1, "Operation not permitted")])
def test_bounded_native_search_survives_kill_helper_oserror(monkeypatch, exc):
    ops = ShellFileOperations(LocalEnvironment())
    if not ops._native_read_enabled():
        pytest.skip("native read lane disabled on this host")

    def _raise(_proc):
        raise exc

    monkeypatch.setattr(local_env, "_kill_process_group_posix", _raise)
    result = ops._run_rg_native(_CHILD_ARGV, 5, 10)
    assert result.exit_code == 0
    assert result.stdout.splitlines() == ["1", "2", "3", "4", "5"]
