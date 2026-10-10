import OAI.Analysis.CircleDomains.Rigidity.ConductivityExterior
import OAI.Analysis.CircleDomains.Rigidity.SmoothReplacementFlux
import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals
import OAI.Analysis.CircleDomains.Rigidity.PrincipalCircleFluxLimit

namespace OAI

/-! The actual weak conductivity height has the principal boundary flux.
The interior correction is constructed, its derivative integral vanishes,
and the smooth Green calculation retains the exact exterior values. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphic_physical_im_smooth {φ : ℂ → ℂ} {F : Set EuclideanPlane}
    (hF : IsClosed F) (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (φ (complexPlaneCoordinates x)).im) Fᶜ := by
  have hO : IsOpen (complexPlaneCoordinates '' F)ᶜ :=
    (complexPlaneCoordinates.toHomeomorph.isClosedMap _ hF).isOpen_compl
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) φ (complexPlaneCoordinates '' F)ᶜ :=
    (hh.contDiffOn hO).restrict_scalars ℝ
  have hp := hc.comp complexPlaneCoordinates.contDiff.contDiffOn
    (show MapsTo complexPlaneCoordinates Fᶜ (complexPlaneCoordinates '' F)ᶜ from by
      intro x hx hm
      obtain ⟨y, hy, heq⟩ := hm
      exact hx (complexPlaneCoordinates.injective heq ▸ hy))
  exact Complex.imCLM.contDiff.contDiffOn.comp hp (mapsTo_univ _ _)

 theorem PlaneLocalWeakComplex.vertical_flux_boundary
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀) (hR : r₀ < R) :
    (∫ x in ball (0 : EuclideanPlane) R, D.imagGradient x 1) =
      planarFormIntegral (fun z => -(φ z).im) (fun _ => 0) (unitCircleParam 0 R) := by
  have hcont := hφ.comp complexPlaneCoordinates.continuous
  obtain ⟨v, e, he, hv, hs, hsub, hue, hext⟩ := exists_smooth_exterior_replacement hF hFr
    (D.imagWitness hcont r₀) (holomorphic_physical_im_smooth hF.isClosed hh)
  have hRpos : 0 < R := hr₀.trans hR
  have hflux := integral_weakGradient_eq_smooth_replacement (D.imagWitness hcont R)
    he hs (hsub.trans (ball_subset_ball hR.le)) hv hue 1
  change (∫ x in ball (0 : EuclideanPlane) R, D.imagGradient x 1) = _ at hflux
  rw [hflux, smooth_physical_disk_vertical_flux hgreen R hRpos hv]
  unfold planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _ht
  have hn : ‖complexPlaneCoordinates.symm (unitCircleParam 0 R t)‖ = R := by
    rw [← complexPlaneCoordinates_norm, ContinuousLinearEquiv.apply_symm_apply]
    simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRpos]
  have hout : complexPlaneCoordinates.symm (unitCircleParam 0 R t) ∉ ball 0 r₀ := by
    simp only [mem_ball, dist_zero_right, hn]
    exact not_lt_of_gt hR
  have hvv := hext hout
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hvv
  simp only [hvv]

 theorem PlaneLocalWeakComplex.vertical_flux_limit
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ => (∫ x in ball (0 : EuclideanPlane) R, D.imagGradient x 1) -
      (volume (ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 (-Real.pi*c.re)) := by
  apply (principal_circle_flux_limit hφ hT hexp).congr'
  filter_upwards [eventually_gt_atTop r₀] with R hR
  rw [D.vertical_flux_boundary hgreen hφ hF hh hr₀ hFr hR,
    physical_real_volume_ball R (hr₀.trans hR).le]

end CircleDomainRigidity

end

end OAI
