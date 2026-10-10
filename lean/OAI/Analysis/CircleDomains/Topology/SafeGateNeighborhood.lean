import OAI.Analysis.CircleDomains.Selection.FiniteGateObstacles
import Mathlib.Topology.Separation.Regular

namespace OAI

/-! A compact forbidden-hit set has a relatively compact neighborhood that
avoids both the anchor and the closed target gate. The map is only required
to be continuous on the actual domain. -/

open Set Function

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

theorem exists_safe_gate_neighborhood
    (U E F : Set X) (hU : IsOpen U) (hE : IsClosed E) (hF : IsCompact F)
    (hFU : F ⊆ U) (hEF : Disjoint E F)
    (f : U → Y) (hf : Continuous f) (Q : Set Y) (hQ : IsClosed Q)
    (hFQ : ∀x : U, x.val ∈ F → f x ∉ Q) :
    ∃S : Set X, IsOpen S ∧ F ⊆ S ∧ closure S ⊆ U ∧
      Disjoint E (closure S) ∧ ∀x : U, x.val ∈ closure S → f x ∉ Q := by
  let V : Set X := Subtype.val '' ((f ⁻¹' Qᶜ) ∩ (Subtype.val ⁻¹' Eᶜ))
  have hVo : IsOpen V := hU.isOpenMap_subtype_val _
    ((hQ.isOpen_compl.preimage hf).inter (hE.isOpen_compl.preimage continuous_subtype_val))
  have hFV : F ⊆ V := by
    intro x hx
    refine ⟨⟨x, hFU hx⟩, ?_, rfl⟩
    exact ⟨hFQ _ hx, fun hxE => Set.disjoint_left.mp hEF hxE hx⟩
  obtain ⟨S, hSo, hFS, hSV⟩ := hF.exists_isOpen_closure_subset (hVo.mem_nhdsSet.mpr hFV)
  refine ⟨S, hSo, hFS, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hSV hx
    exact y.property
  · apply Set.disjoint_left.mpr
    intro x hxE hxS
    obtain ⟨y, hy, heq⟩ := hSV hxS
    exact hy.2 (heq.symm ▸ hxE)
  · intro x hx
    obtain ⟨y, hy, heq⟩ := hSV hx
    have hyx : y = x := Subtype.ext heq
    exact hyx ▸ hy.1

end CircleDomainRigidity

end OAI
