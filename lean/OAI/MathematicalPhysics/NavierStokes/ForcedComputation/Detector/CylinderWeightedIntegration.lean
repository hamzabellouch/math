import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderDivergence
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularLift

namespace OAI

/-! Weighted divergence identity for the horizontal cutoffs in the
cylinder energy calculation. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

theorem integrable_space_function {g : Space → ℝ} (hg : Continuous g)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ x, horizontal x ∉ K → g x = 0) :
    Integrable (fun y => g (atHeight y.1 y.2)) cylinderMeasure := by
  apply integrable_horizontal_compact (hg.comp atHeight_smooth.continuous) hK
  intro y hy
  apply hs
  simpa only [atHeight_horizontal] using hy

theorem divergence_continuous {U : Space → Space} (hU : ContDiff ℝ 1 U) :
    Continuous (divergence U) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_apply j).comp
    ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem weighted_integrable {φ : Plane → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {g : Space → ℝ} (hg : Continuous g) :
    Integrable (fun y => φ y.1 * g (atHeight y.1 y.2)) cylinderMeasure := by
  have hi := integrable_space_function (g := fun x => φ (horizontalLinear x) * g x)
    ((hφ.comp horizontalLinear.continuous).mul hg) hc
    (fun x hx => by rw [horizontalLinear_eq, image_eq_zero_of_notMem_tsupport hx, zero_mul])
  simpa only [horizontalLinear_eq, atHeight_horizontal] using hi

theorem weight_derivative_integrable {φ : Plane → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) {U : Space → Space} (hU : Continuous U) :
    Integrable (fun y => fderiv ℝ φ y.1 (horizontalLinear (U (atHeight y.1 y.2))))
      cylinderMeasure := by
  have hi := integrable_space_function
    (g := fun x => fderiv ℝ φ (horizontalLinear x) (horizontalLinear (U x)))
    (((hφ.continuous_fderiv (by norm_num)).comp horizontalLinear.continuous).clm_apply
      (horizontalLinear.continuous.comp hU)) hc (fun x hx => by
        rw [horizontalLinear_eq, fderiv_of_notMem_tsupport ℝ hx]
        rfl)
  simpa only [horizontalLinear_eq, atHeight_horizontal] using hi

theorem integral_weighted_divergence {φ : Plane → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) {U : Space → Space} (hU : ContDiff ℝ 1 U)
    (hp : VerticallyPeriodic U) :
    (∫ y, φ y.1 * divergence U (atHeight y.1 y.2) ∂cylinderMeasure) =
      -(∫ y, fderiv ℝ φ y.1 (horizontalLinear (U (atHeight y.1 y.2)))
        ∂cylinderMeasure) := by
  let ψ : Space → ℝ := fun x => φ (horizontalLinear x)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp horizontalLinear.contDiff
  have hψ0 (x : Space) (hx : horizontal x ∉ tsupport φ) : ψ x = 0 := by
    dsimp only [ψ]
    rw [horizontalLinear_eq]
    exact image_eq_zero_of_notMem_tsupport hx
  have hz := integral_divergence_zero (U := fun x => ψ x • U x) (hψ.smul hU) hc
    (fun x hx => by simp only [hψ0 x hx, zero_smul])
    (fun x n => by
      change φ (horizontalLinear (x + (n : ℝ) • basis 2)) • U (x + (n : ℝ) • basis 2) = _
      rw [map_add, map_smul, horizontalLinear_basis_two, smul_zero, add_zero, hp])
  have he (x : Space) : divergence (fun y => ψ y • U y) x =
      ψ x * divergence U x + fderiv ℝ φ (horizontalLinear x) (horizontalLinear (U x)) := by
    rw [divergence_scalar_mul (hψ.differentiable (by norm_num))
      (hU.differentiable (by norm_num))]
    have hd := (hφ.differentiable (by norm_num) (horizontalLinear x)).hasFDerivAt.comp x
      horizontalLinear.hasFDerivAt
    change HasFDerivAt ψ _ x at hd
    rw [hd.fderiv]
    rfl
  have hi : Integrable (fun y => ψ (atHeight y.1 y.2) *
      divergence U (atHeight y.1 y.2)) cylinderMeasure :=
    integrable_space_function (g := fun x => ψ x * divergence U x)
      (hψ.continuous.mul (divergence_continuous hU)) hc
      (fun x hx => by rw [hψ0 x hx, zero_mul])
  have hj : Integrable (fun y => fderiv ℝ φ (horizontalLinear (atHeight y.1 y.2))
      (horizontalLinear (U (atHeight y.1 y.2)))) cylinderMeasure := by
    apply integrable_space_function
      (g := fun x => fderiv ℝ φ (horizontalLinear x) (horizontalLinear (U x)))
      (((hφ.continuous_fderiv (by norm_num)).comp horizontalLinear.continuous).clm_apply
        (horizontalLinear.continuous.comp hU.continuous)) hc
    intro x hx
    rw [horizontalLinear_eq, fderiv_of_notMem_tsupport ℝ hx]
    rfl
  simp_rw [he] at hz
  rw [integral_add hi hj] at hz
  simp only [ψ, horizontalLinear_eq, atHeight_horizontal] at hz
  simp only [horizontalLinear_eq]
  linarith

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
