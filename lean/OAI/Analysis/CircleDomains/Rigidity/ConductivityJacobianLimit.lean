import OAI.Analysis.CircleDomains.Rigidity.ConductivityJacobianBoundary
import OAI.Analysis.CircleDomains.Sobolev.PrincipalCircleAreaLimit

namespace OAI

/-! The actual weak Jacobian has vanishing area defect at infinity. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.jacobian_area_limit
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ =>
      (∫ x in ball (0 : EuclideanPlane) R,
        D.realGradient x 0 * D.imagGradient x 1 -
          D.realGradient x 1 * D.imagGradient x 0) -
        (volume (ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 0) := by
  apply (principal_circle_area_limit hT hexp).congr'
  filter_upwards [eventually_gt_atTop r₀] with R hR
  rw [D.jacobian_boundary hgreen hφ hF hh hr₀ hFr hR,
    physical_real_volume_ball R (hr₀.trans hR).le]
  rfl

end CircleDomainRigidity

end

end OAI
