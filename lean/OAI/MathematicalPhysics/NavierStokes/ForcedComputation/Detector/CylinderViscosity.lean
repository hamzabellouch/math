import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderWeightCalculus
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderPressureTransport
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyComparison

namespace OAI

/-! The two divergence computations used for the viscous part of the
localized cylinder energy identity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

def diffusionFlux (W : Space → Space) (x : Space) : Space :=
  fun j => dot (W x) (derivative W j x)

theorem diffusionFlux_regular {W : Space → Space} (hW : ContDiff ℝ 2 W) :
    ContDiff ℝ 1 (diffusionFlux W) := by
  apply contDiff_pi.mpr
  intro j
  exact dot_contDiff (hW.of_le (by norm_num)) (derivative_contDiff hW j)

theorem diffusionFlux_continuous {W : Space → Space} (hW : ContDiff ℝ 1 W) :
    Continuous (diffusionFlux W) := by
  apply continuous_pi
  intro j
  exact dot_continuous hW.continuous
    ((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem diffusionFlux_periodic {W : Space → Space} (hW : ContDiff ℝ 2 W)
    (hp : VerticallyPeriodic W) : VerticallyPeriodic (diffusionFlux W) := by
  have hd := verticallyPeriodic_fderiv hp (hW.differentiable (by norm_num))
  intro x n
  ext j
  simp only [diffusionFlux, derivative, hp x n, hd x n]

theorem density_gradient_pairing {W : Space → Space} (hW : ContDiff ℝ 1 W)
    (ψ : Space → ℝ) (x : Space) :
    fderiv ℝ (fun y => dot (W y) (W y)) x (ShearFlows.gradient ψ x) =
      2 * fderiv ℝ ψ x (diffusionFlux W x) := by
  rw [← coordinate_trace (fderiv ℝ (fun y => dot (W y) (W y)) x)
    (ShearFlows.gradient ψ x), ← coordinate_trace (fderiv ℝ ψ x) (diffusionFlux W x)]
  simp only [ShearFlows.gradient, fderiv_dot_self (hW.differentiable (by norm_num)),
    diffusionFlux, derivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diffusionFlux_divergence {W : Space → Space} (hW : ContDiff ℝ 2 W) (x : Space) :
    divergence (diffusionFlux W) x =
      (∑ j, dot (derivative W j x) (derivative W j x)) + dot (W x) (laplacian W x) :=
  divergence_dot_derivative hW x

theorem diffusion_boundary_pairing {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {W : Space → Space} (hW : ContDiff ℝ 1 W)
    (hp : VerticallyPeriodic W) :
    2 * (∫ y, fderiv ℝ φ y.1 (horizontalLinear (diffusionFlux W (atHeight y.1 y.2)))
      ∂cylinderMeasure) =
    -(∫ y, VelocityDetector.scalarLaplacian φ y.1 *
      dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2)) ∂cylinderMeasure) := by
  let ψ := scalarPlaneLift φ
  let G : Space → Space := fun x => dot (W x) (W x) • ShearFlows.gradient ψ x
  have hG : ContDiff ℝ 1 G :=
    (dot_contDiff hW hW).smul ((lifted_gradient_smooth hφ).of_le (by simp))
  have hGp : VerticallyPeriodic G := by
    intro x n
    dsimp only [G]
    rw [hp, lifted_gradient_periodic hφ]
  have hz := integral_divergence_zero hG hc
    (fun x hx => by
      change dot (W x) (W x) • ShearFlows.gradient (scalarPlaneLift φ) x = 0
      rw [lifted_gradient_support x hx, smul_zero]) hGp
  have he (x : Space) : divergence G x =
      VelocityDetector.scalarLaplacian φ (horizontalLinear x) * dot (W x) (W x) +
        2 * fderiv ℝ φ (horizontalLinear x) (horizontalLinear (diffusionFlux W x)) := by
    rw [show G = (fun x => dot (W x) (W x) • ShearFlows.gradient ψ x) from rfl,
      divergence_scalar_mul ((dot_contDiff hW hW).differentiable (by norm_num))
        ((lifted_gradient_smooth hφ).differentiable (by simp))]
    rw [lifted_gradient_divergence hφ, density_gradient_pairing hW]
    have hd := (hφ.differentiable (by simp) (horizontalLinear x)).hasFDerivAt.comp x
      horizontalLinear.hasFDerivAt
    change HasFDerivAt ψ _ x at hd
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    ring
  have hi := weighted_integrable (ExpandingDetector.scalarLaplacian_smooth hφ).continuous
    (ExpandingDetector.scalarLaplacian_compactSupport hc) (dot_continuous hW.continuous hW.continuous)
  have hj := weight_derivative_integrable (hφ.of_le (by simp)) hc
    (diffusionFlux_continuous hW)
  have hl (a : Plane) (b : ℝ) : horizontalLinear (atHeight a b) = a := by
    rw [horizontalLinear_eq, atHeight_horizontal]
  simp_rw [he, hl] at hz
  rw [integral_add hi (hj.const_mul 2), integral_const_mul] at hz
  linarith

theorem viscosity_pairing {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {W : Space → Space} (hW : ContDiff ℝ 2 W)
    (hp : VerticallyPeriodic W) :
    2 * (∫ y, φ y.1 * dot (W (atHeight y.1 y.2)) (laplacian W (atHeight y.1 y.2))
      ∂cylinderMeasure) =
      -2 * (∫ y, φ y.1 * ∑ j, dot (derivative W j (atHeight y.1 y.2))
        (derivative W j (atHeight y.1 y.2)) ∂cylinderMeasure) +
      (∫ y, VelocityDetector.scalarLaplacian φ y.1 *
        dot (W (atHeight y.1 y.2)) (W (atHeight y.1 y.2)) ∂cylinderMeasure) := by
  have hA := weighted_integrable hφ.continuous hc
    (continuous_finsetSum Finset.univ (fun j _ => dot_continuous
      (derivative_contDiff hW j).continuous (derivative_contDiff hW j).continuous))
  have hB := weighted_integrable hφ.continuous hc
    (dot_continuous hW.continuous (laplacian_continuous hW))
  have h := integral_weighted_divergence (hφ.of_le (by simp)) hc
    (diffusionFlux_regular hW) (diffusionFlux_periodic hW hp)
  simp_rw [diffusionFlux_divergence hW, mul_add] at h
  rw [integral_add hA hB] at h
  have hboundary := diffusion_boundary_pairing hφ hc (hW.of_le (by norm_num)) hp
  linarith

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
