import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace OAI

/-! Convert the standard library's cycle walks into exact cycle witnesses. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V}

theorem hasCycle_of_isCycle {x : V} {p : G.Walk x x} (hp : p.IsCycle) :
    HasCycle G p.length := by
  refine ⟨fun i => p.getVert i.val, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) hij
  · intro i
    have hadj := p.adj_getVert_succ i.isLt
    by_cases hlast : i.val + 1 = p.length
    · have hn : (cycleNext i).val = 0 := by simp [cycleNext, hlast]
      simpa [hlast, hn] using hadj
    · have hn : (cycleNext i).val = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      simpa [hn] using hadj

/-- A simple path of at least two edges closes to an exact cycle when its
endpoints are adjacent. This is the single-chain case of path closure. -/
theorem hasCycle_of_path_close {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) (hlen : 2 ≤ p.length) (hclose : G.Adj y x) :
    HasCycle G (p.length + 1) := by
  have hdis : p.support.tail.Disjoint hclose.toWalk.support.tail := by
    rw [hclose.support_toWalk]
    apply List.disjoint_left.mpr
    intro v hv hvx
    have hv' : v = x := by simpa using hvx
    subst v
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1 hv
  have hcycle := hp.isCycle_append hclose.isPath_toWalk hdis (Or.inl (by omega))
  have hc := hasCycle_of_isCycle hcycle
  simpa using hc

end CycleClique.Construction

end OAI
