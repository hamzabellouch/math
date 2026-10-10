import OAI.Combinatorics.MatchingCount.Sampling.Certify

namespace OAI

/-! # Explicit least roots of finite graph components

The selector uses the finite reachability closure, not a choice of a
quotient representative. Its defining closure runs exactly n growth
rounds on Fin n, including disconnected and singleton components.
-/

namespace ContingencyTables.FiniteGraphRoots

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma closure_nonempty (v : Fin n) : (closure G v).Nonempty :=
  ⟨v,(mem_closure G v v).mpr (Reachable.refl v)⟩

/-- The least actual vertex index in the reached component. -/
def root (v : Fin n) : Fin n := (closure G v).min' (closure_nonempty G v)

lemma root_mem (v : Fin n) : root G v∈closure G v :=
  Finset.min'_mem _ _

lemma root_reachable (v : Fin n) : G.Reachable v (root G v) :=
  (mem_closure G v (root G v)).mp (root_mem G v)

lemma closure_eq {u v : Fin n} (h : G.Reachable u v) : closure G u=closure G v := by
  ext a
  simp only [mem_closure]
  constructor
  · intro hu
    exact h.symm.trans hu
  · intro hv
    exact h.trans hv

lemma root_constant {u v : Fin n} (h : G.Reachable u v) : root G u=root G v := by
  apply le_antisymm
  · exact Finset.min'_le _ _ ((mem_closure G u (root G v)).mpr
      (h.trans (root_reachable G v)))
  · exact Finset.min'_le _ _ ((mem_closure G v (root G u)).mpr
      (h.symm.trans (root_reachable G u)))

lemma root_idempotent (v : Fin n) : root G (root G v)=root G v :=
  (root_constant G (root_reachable G v)).symm

lemma root_le {u v : Fin n} (h : G.Reachable u v) : root G u≤v :=
  Finset.min'_le _ v ((mem_closure G u v).mpr h)

lemma root_eq_self_of_minimal (u : Fin n)
    (h : ∀ v,G.Reachable u v → u≤v) : root G u=u := by
  apply le_antisymm
  · exact root_le G (Reachable.refl u)
  · exact h _ (root_reachable G u)

end ContingencyTables.FiniteGraphRoots

end OAI
