import OAI.Analysis.CircleDomains.Topology.PathGates

namespace OAI

/-! Hit-location restrictions are avoidance of the union of forbidden
parts of the prescribed contours. No closedness is needed for this identity. -/

open Set Function

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def gateForbiddenSet (C K : ℕ → Set X) : Set X := ⋃i, C i \ K i

theorem gateRules_iff_avoids (C K : ℕ → Set X) (γ : C(PathTime, X)) :
    GateRules C K γ ↔ ∀t, γ t ∉ gateForbiddenSet C K := by
  constructor
  · intro h t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hi.2 (h i t hi.1)
  · intro h i t ht
    by_contra hn
    exact h t (mem_iUnion.mpr ⟨i, ht, hn⟩)

omit [MetricSpace X] in
theorem avoids_gateForbiddenSet_of_avoids_contours
    (C K : ℕ → Set X) {x : X} (h : ∀i, x ∉ C i) : x ∉ gateForbiddenSet C K := by
  intro hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact h i hi.1

end CircleDomainRigidity

end OAI
