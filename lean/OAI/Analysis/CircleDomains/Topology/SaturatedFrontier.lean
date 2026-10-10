import OAI.Analysis.CircleDomains.Topology.SaturatedDisks

namespace OAI

/-! A saturated open set with closed projected closure has its exact projected
frontier. This identifies the boundary of the quotient collars. -/

open Set Function

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem frontier_image_of_saturated_open (π : X → Y) (hπ : Continuous π)
    (U : Set X) (hU : IsOpen U) (ho : IsOpen (π '' U))
    (hc : IsClosed (π '' closure U)) (hsat : π ⁻¹' (π '' U) = U) :
    frontier (π '' U) = π '' frontier U := by
  have hcl : closure (π '' U) = π '' closure U := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hc
    · exact image_closure_subset_closure_image hπ
  rw [ho.frontier_eq, hcl, hU.frontier_eq]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun h => hy ⟨x, h, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro h
    exact hxn (hsat ▸ h)

end CircleDomainRigidity

end OAI
