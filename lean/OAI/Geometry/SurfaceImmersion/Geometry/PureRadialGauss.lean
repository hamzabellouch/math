import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateGauss
import OAI.Geometry.SurfaceImmersion.Geometry.PreparedRadialSecondForm

namespace OAI

/-! The curvature in the initial ordered crossing invariant is the actual
Gaussian curvature computed from the induced metric, rather than a freely
specified scalar. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame

def coordinateGaussianCurvature (E F G : Base → ℝ) (p : Base) : ℝ :=
  coordinateGauss E F G p/(E p*G p-(F p)^2)

lemma coordinateGauss_pure_radial {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (n : RVec 4) {r : ℝ}
    (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ v w, realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      (r⁻¹)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
  rw [← gauss_metric_identity hF p hD,hB dx dx,hB dy dy,hB dx dy]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,mul_one,NormalFrame.gramDet]
  ring

lemma coordinateGaussianCurvature_pure_radial {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (n : RVec 4) {r : ℝ} (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ v w, realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      (r⁻¹)^2 := by
  rw [coordinateGaussianCurvature,coordinateGauss_pure_radial hF p n hn hD hB]
  change (r⁻¹)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p)/
    gramDet (coordDeriv dx F p) (coordDeriv dy F p) = _
  exact mul_div_cancel_right₀ _ hD

theorem orderedCrossing_intrinsic_pure_radial {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (n : RVec 4) {r : ℝ} (hr : 0 < r) (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ a b, realSecondForm F a b p =
      (r⁻¹*(coordDeriv a F p ⬝ᵥ coordDeriv b F p)) • n)
    (hv : coordDeriv v F p ≠ 0) (hw : coordDeriv w F p ≠ 0) :
    0 < orderedCrossing F v w p
      (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) := by
  rw [coordinateGaussianCurvature_pure_radial hF p n hn hD hB]
  exact (orderedCrossing_pure_radial p v w n hr hn hv hw (hB v v) (hB v w)).2

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4
open RealModes SmallModes SphericalJets

theorem scaled_flat_spherical_intrinsic_crossing {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) {r : ℝ} (hr : 0 < r) (x : SmallModes.Base)
    (hunit : ‖F (planeCoordinates.symm x)‖ = 1)
    (hflat : ∀ v w, sphericalSecondForm F (planeCoordinates.symm x) v w = 0)
    (hI : Function.Injective (fderiv ℝ (scaledSphereCoordinates F r) x))
    {v w : SmallModes.Base} (hv : v ≠ 0) (hw : w ≠ 0) :
    0 < VelocityFrame.orderedCrossing (scaledSphereCoordinates F r) v w x
      (coordinateGaussianCurvature (realMetric (scaledSphereCoordinates F r) dx dx)
        (realMetric (scaledSphereCoordinates F r) dx dy)
        (realMetric (scaledSphereCoordinates F r) dy dy) x) := by
  have hn : spaceCoordinates (-F (planeCoordinates.symm x)) ⬝ᵥ
      spaceCoordinates (-F (planeCoordinates.symm x)) = 1 := by
    rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,norm_neg,hunit]
    norm_num
  have hs : ContDiff ℝ ∞ (scaledSphereCoordinates F r) :=
    spaceCoordinates.contDiff.comp ((hF.const_smul r).comp planeCoordinates.symm.contDiff)
  apply orderedCrossing_intrinsic_pure_radial hs x v w _ hr hn
    (gramDet_ne_zero_of_injective _ hI)
    (scaled_flat_spherical_secondForm hF hr.ne' x hflat (gramDet_ne_zero_of_injective _ hI))
  · intro hz
    exact hv (hI (by simpa only [coordDeriv,map_zero] using hz))
  · intro hz
    exact hw (hI (by simpa only [coordDeriv,map_zero] using hz))

end ClosedSurfaceR4

end

end OAI
