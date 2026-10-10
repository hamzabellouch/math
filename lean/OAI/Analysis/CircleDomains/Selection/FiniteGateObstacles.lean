import OAI.Analysis.CircleDomains.Selection.GateForbiddenSet

namespace OAI

/-! The forbidden portions of finitely many prescribed gates form a compact
obstacle, and failure of those gates is exactly a hit of this obstacle. -/

open Set Function

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def finiteGateForbiddenSet (k : ℕ) (C K : ℕ → Set X) : Set X :=
  ⋃i : Fin (k+1), C i.val \ K i.val

theorem isCompact_finiteGateForbiddenSet (k : ℕ) (C K : ℕ → Set X)
    (hC : ∀j ≤ k, IsCompact (C j)) (hK : ∀j ≤ k, IsOpen (K j)) :
    IsCompact (finiteGateForbiddenSet k C K) := by
  apply isCompact_iUnion
  intro i
  exact (hC i.val (by omega)).inter_right (hK i.val (by omega)).isClosed_compl

theorem finiteGateRules_iff_avoids (k : ℕ) (C K : ℕ → Set X) (γ : C(PathTime, X)) :
    (∀j ≤ k, GateRule (C j) (K j) γ) ↔ ∀t, γ t ∉ finiteGateForbiddenSet k C K := by
  constructor
  · intro h t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hi.2 (h i.val (by omega) t hi.1)
  · intro h j hj t ht
    by_contra hn
    exact h t (mem_iUnion.mpr ⟨⟨j, by omega⟩, ht, hn⟩)

theorem exists_forbidden_hit_of_not_finiteGateRules
    (k : ℕ) (C K : ℕ → Set X) (γ : C(PathTime, X))
    (h : ¬ ∀j ≤ k, GateRule (C j) (K j) γ) :
    ∃t, γ t ∈ finiteGateForbiddenSet k C K := by
  classical
  rw [finiteGateRules_iff_avoids] at h
  simpa only [not_forall, not_not] using h

end CircleDomainRigidity

end OAI
