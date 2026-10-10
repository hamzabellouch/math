import OAI.Geometry.IsometricImmersion.Curvature.IntrinsicCurvature
import OAI.Geometry.IsometricImmersion.Calculus.HessianCommutator
import Mathlib.Tactic.LinearCombination

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem covHessian_coordPartial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (d i j : Fin 2) :
    coordPartial d (fun q => covHessian g z q i j) p =
      coordPartial d (fun q => covHessian g z q j i) p := by
  have heq : (fun q => covHessian g z q i j) =ᶠ[𝓝 p]
      (fun q => covHessian g z q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact covHessian_symm hg hU hz hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem hessian_transport_Ay_Bx
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) :
    coordPartial 1 (fun q => covHessian g z q 0 0) p -
        coordPartial 0 (fun q => covHessian g z q 0 1) p =
      christoffel g 0 0 1 p * covHessian g z p 0 0 +
        (christoffel g 1 0 1 p - christoffel g 0 0 0 p) * covHessian g z p 0 1 -
        christoffel g 1 0 0 p * covHessian g z p 1 1 +
        gaussianCurvature g p * (g p 0 1 * coordPartial 0 z p -
          g p 0 0 * coordPartial 1 z p) := by
  have hc := covHessian_commutator hg hU hz hp 0 1 0
  simp only [covDerivHessian, Fin.sum_univ_two, riemann_factorization hg hU hp] at hc
  simp [curvatureFactor] at hc
  simp only [covHessian_coordPartial_symm hg hU hz hp 0 1 0,
    covHessian_symm hg hU hz hp 1 0,
    christoffel_lower_symm hg hU hp 0 1 0,
    christoffel_lower_symm hg hU hp 1 1 0,
    metric_coeff_symm hg hp 1 0] at hc
  linear_combination -hc

theorem hessian_transport_hx_By
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) :
    coordPartial 0 (fun q => covHessian g z q 1 1) p -
        coordPartial 1 (fun q => covHessian g z q 0 1) p =
      -christoffel g 0 1 1 p * covHessian g z p 0 0 +
        (christoffel g 0 0 1 p - christoffel g 1 1 1 p) * covHessian g z p 0 1 +
        christoffel g 1 0 1 p * covHessian g z p 1 1 +
        gaussianCurvature g p * (g p 0 1 * coordPartial 1 z p -
          g p 1 1 * coordPartial 0 z p) := by
  have hc := covHessian_commutator hg hU hz hp 0 1 1
  simp only [covDerivHessian, Fin.sum_univ_two, riemann_factorization hg hU hp] at hc
  simp [curvatureFactor] at hc
  simp only [covHessian_symm hg hU hz hp 1 0,
    christoffel_lower_symm hg hU hp 0 1 0,
    christoffel_lower_symm hg hU hp 1 1 0] at hc
  linear_combination hc

theorem darboux_determinant_derivative
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ q ∈ U, (covHessian g z q).det =
      gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (d : Fin 2) :
    coordPartial d (fun q => covHessian g z q 0 0) p * covHessian g z p 1 1 +
        covHessian g z p 0 0 * coordPartial d (fun q => covHessian g z q 1 1) p -
        2 * covHessian g z p 0 1 * coordPartial d (fun q => covHessian g z q 0 1) p =
      coordPartial d (gaussianCurvature g) p * heightEnergy g z p +
        gaussianCurvature g p * coordPartial d (heightEnergy g z) p := by
  have heq : (fun q => covHessian g z q 0 0 * covHessian g z q 1 1 -
      covHessian g z q 0 1 * covHessian g z q 0 1) =ᶠ[𝓝 p]
      (fun q => gaussianCurvature g q * heightEnergy g z q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hq 1 0] using hDarboux q hq
  have hdH (i j : Fin 2) : DifferentiableAt ℝ (fun q => covHessian g z q i j) p :=
    (((covHessian_contDiffOn hg hU hz i j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdK : DifferentiableAt ℝ (gaussianCurvature g) p :=
    (((gaussianCurvature_contDiffOn hg hU) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdE : DifferentiableAt ℝ (heightEnergy g z) p :=
    (((heightEnergy_contDiffOn hg hU hz) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hd : coordPartial d
      (fun q => covHessian g z q 0 0 * covHessian g z q 1 1 -
        covHessian g z q 0 1 * covHessian g z q 0 1) p =
      coordPartial d (fun q => gaussianCurvature g q * heightEnergy g z q) p := by
    unfold coordPartial
    rw [heq.fderiv_eq]
  have hdprod : DifferentiableAt ℝ
      (fun q => covHessian g z q 0 0 * covHessian g z q 1 1) p :=
    (hdH 0 0).mul (hdH 1 1)
  have hdsq : DifferentiableAt ℝ
      (fun q => covHessian g z q 0 1 * covHessian g z q 0 1) p :=
    (hdH 0 1).mul (hdH 0 1)
  rw [HessianCalculus.coordPartial_sub_at hdprod hdsq d,
    HessianCalculus.coordPartial_mul_at (hdH 0 0) (hdH 1 1) d,
    HessianCalculus.coordPartial_mul_at (hdH 0 1) (hdH 0 1) d,
    HessianCalculus.coordPartial_mul_at hdK hdE d] at hd
  linear_combination hd

end SmoothLocal.Geometry

end

end OAI
