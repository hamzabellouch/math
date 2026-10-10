import OAI.Analysis.CircleDomains.Reflection.UnitAnalyticJordanParametrization
import OAI.Analysis.CircleDomains.Transfer.GlobalCoreExtension

namespace OAI

/-! A fixed analytic source collar for a chosen actual hole. Its outer
side lies in the multiply connected domain and avoids every other cap. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

lemma exists_analytic_boundary_collar (C:FiniteJordanConfiguration I) (i:I)
    (ha:IsAnalyticJordanCap (C.hole i)) :
    ∃R:ℝ, ∃β:ℂ→ℂ, 1<R ∧
      DifferentiableOn ℂ β (symmetricCircleAnnulus R) ∧
      InjOn β (symmetricCircleAnnulus R) ∧
      β '' sphere 0 1=frontier (jordanInterior (C.hole i)) ∧
      (∀z∈symmetricCircleAnnulus R,1<‖z‖ → (β z:Sphere)∈C.region) ∧
      (∀z∈symmetricCircleAnnulus R,1≤‖z‖ → (β z:Sphere)∈closure C.region) := by
  obtain ⟨S,β,hS,hDS,hβ,hi,hclosed,hboundary⟩ :=
    exists_unit_analytic_jordan_parametrization ha
  let B : Set ℂ := ⋃j:{j:I // j≠i},closure (jordanInterior (C.hole j))
  have hB : IsClosed B := isClosed_iUnion_of_finite fun _ => isClosed_closure
  let T := S∩β ⁻¹' Bᶜ
  have hT : IsOpen T := hβ.continuousOn.isOpen_inter_preimage hS hB.isOpen_compl
  have hcircle : sphere (0:ℂ) 1⊆T := by
    intro z hz
    refine ⟨hDS (sphere_subset_closedBall hz),?_⟩
    intro hzB
    obtain ⟨j,hj⟩ := mem_iUnion.mp hzB
    have hzi : β z∈closure (jordanInterior (C.hole i)) :=
      frontier_subset_closure (hboundary ▸ mem_image_of_mem β hz)
    exact Set.disjoint_left.mp (C.disjoint j.property.symm) hzi hj
  obtain ⟨R,hR,hRT⟩ := exists_symmetricCircleAnnulus_subset hT hcircle
  have hout : ∀z∈symmetricCircleAnnulus R,1<‖z‖ → (β z:Sphere)∈C.region := by
    intro z hz hzn hp
    obtain ⟨j,w,hw,he⟩ := mem_iUnion.mp hp
    have hwb : w=β z := OnePoint.coe_injective he
    subst w
    by_cases hji : j=i
    · subst j
      rw [←hclosed] at hw
      obtain ⟨w,hw,he⟩ := hw
      have hwz : w=z := hi (hDS hw) (hRT hz).1 he
      rw [hwz] at hw
      exact (not_le_of_gt hzn) (mem_closedBall_zero_iff.mp hw)
    · exact (hRT hz).2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hw⟩)
  refine ⟨R,β,hR,hβ.mono (hRT.trans inter_subset_left),
    hi.mono (hRT.trans inter_subset_left),hboundary,hout,?_⟩
  intro z hz hzn
  rcases eq_or_lt_of_le hzn with he|he
  · apply C.boundary_subset_closure_region i
    rw [frontier_closedTerminalCap]
    exact ⟨β z,hboundary ▸ mem_image_of_mem β (mem_sphere_zero_iff_norm.mpr he.symm),rfl⟩
  · exact subset_closure (hout z hz he)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
