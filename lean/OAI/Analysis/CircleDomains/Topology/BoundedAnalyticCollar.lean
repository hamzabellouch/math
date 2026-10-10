import OAI.Analysis.CircleDomains.Reflection.AnalyticConfigurationCollar

namespace OAI

/-! The source collar is chosen with compact closure inside the analytic
chart. Its physical image has one finite bound for every later model. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

lemma exists_bounded_analytic_boundary_collar (C:FiniteJordanConfiguration I) (i:I)
    (ha:IsAnalyticJordanCap (C.hole i)) :
    ∃R L:ℝ, ∃β:ℂ→ℂ, 1<R ∧ 0<L ∧
      DifferentiableOn ℂ β (symmetricCircleAnnulus R) ∧
      InjOn β (symmetricCircleAnnulus R) ∧
      β '' sphere 0 1=frontier (jordanInterior (C.hole i)) ∧
      (∀z∈symmetricCircleAnnulus R,‖β z‖≤L) ∧
      (∀z∈symmetricCircleAnnulus R,1<‖z‖ → (β z:Sphere)∈C.region) ∧
      (∀z∈symmetricCircleAnnulus R,1≤‖z‖ → (β z:Sphere)∈closure C.region) := by
  obtain ⟨R₀,β,hR₀,hβ,hi,hb,ho,hc⟩ := C.exists_analytic_boundary_collar i ha
  obtain ⟨V,hV,hcircle,hcl,hK⟩ := exists_open_between_and_isCompact_closure
    (isCompact_sphere (0:ℂ) 1) (isOpen_symmetricCircleAnnulus R₀)
    (unit_circle_subset_symmetricCircleAnnulus hR₀)
  obtain ⟨R,hR,hRV⟩ := exists_symmetricCircleAnnulus_subset hV hcircle
  have hsub : symmetricCircleAnnulus R⊆symmetricCircleAnnulus R₀ :=
    hRV.trans (subset_closure.trans hcl)
  obtain ⟨L,hL,hbound⟩ := (hK.image_of_continuousOn (hβ.continuousOn.mono hcl)).isBounded.exists_pos_norm_lt
  refine ⟨R,L,β,hR,hL,hβ.mono hsub,hi.mono hsub,hb,?_,?_,?_⟩
  · intro z hz
    exact (hbound (β z) ⟨z,subset_closure (hRV hz),rfl⟩).le
  · intro z hz
    exact ho z (hsub hz)
  · intro z hz
    exact hc z (hsub hz)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
