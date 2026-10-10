import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderWeightedIntegration

namespace OAI

/-! The pressure and incompressible-transport terms in the localized
difference-energy identity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

theorem pressure_pairing {φ : Plane → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) {W : Space → Space} {p : Space → ℝ}
    (hW : ContDiff ℝ 1 W) (hp : ContDiff ℝ 1 p)
    (hWp : VerticallyPeriodic W) (hpp : VerticallyPeriodic p)
    (hdiv : ∀ x, divergence W x = 0) :
    (∫ y, φ y.1 * dot (W (atHeight y.1 y.2)) (gradient p (atHeight y.1 y.2))
      ∂cylinderMeasure) =
    -(∫ y, p (atHeight y.1 y.2) *
      fderiv ℝ φ y.1 (horizontalLinear (W (atHeight y.1 y.2))) ∂cylinderMeasure) := by
  have he (x : Space) : divergence (fun y => p y • W y) x =
      dot (W x) (gradient p x) := by
    rw [divergence_scalar_mul (hp.differentiable (by norm_num))
      (hW.differentiable (by norm_num)), hdiv, mul_zero, zero_add]
    exact (coordinate_trace (fderiv ℝ p x) (W x)).symm.trans
      (by simp only [dot, ShearFlows.gradient, mul_comm])
  have h := integral_weighted_divergence (U := fun x => p x • W x) hφ hc (hp.smul hW)
    (fun x n => by
      change p (x + (n : ℝ) • basis 2) • W (x + (n : ℝ) • basis 2) = p x • W x
      rw [hpp, hWp])
  simpa only [he, map_smul, smul_eq_mul] using h

theorem transport_pairing {φ : Plane → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) {W V : Space → Space}
    (hW : ContDiff ℝ 1 W) (hV : ContDiff ℝ 1 V)
    (hWp : VerticallyPeriodic W) (hVp : VerticallyPeriodic V)
    (hdiv : ∀ x, divergence V x = 0) :
    2 * (∫ y, φ y.1 * dot (W (atHeight y.1 y.2))
      (fderiv ℝ W (atHeight y.1 y.2) (V (atHeight y.1 y.2))) ∂cylinderMeasure) =
    -(∫ y, fderiv ℝ φ y.1 (horizontalLinear (V (atHeight y.1 y.2))) *
      dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2)) ∂cylinderMeasure) := by
  have he (x : Space) : divergence (fun y => dot (W y) (W y) • V y) x =
      2 * dot (W x) (fderiv ℝ W x (V x)) := by
    rw [divergence_scalar_mul ((dot_contDiff hW hW).differentiable (by norm_num))
      (hV.differentiable (by norm_num)), hdiv, mul_zero, zero_add,
      fderiv_dot_self (hW.differentiable (by norm_num))]
  have h := integral_weighted_divergence (U := fun x => dot (W x) (W x) • V x)
    hφ hc ((dot_contDiff hW hW).smul hV)
    (fun x n => by
      change dot (W (x + (n : ℝ) • basis 2)) (W (x + (n : ℝ) • basis 2)) •
        V (x + (n : ℝ) • basis 2) = dot (W x) (W x) • V x
      rw [hWp, hVp])
  simp only [he, map_smul, smul_eq_mul] at h
  have hi : (fun y : Plane × ℝ => φ y.1 *
      (2 * dot (W (atHeight y.1 y.2))
        (fderiv ℝ W (atHeight y.1 y.2) (V (atHeight y.1 y.2))))) =
      (fun y => 2 * (φ y.1 * dot (W (atHeight y.1 y.2))
        (fderiv ℝ W (atHeight y.1 y.2) (V (atHeight y.1 y.2))))) := by
    funext y
    ring
  rw [hi, integral_const_mul] at h
  simpa only [mul_comm] using h

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
