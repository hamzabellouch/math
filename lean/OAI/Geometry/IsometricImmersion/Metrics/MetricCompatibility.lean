import OAI.Geometry.IsometricImmersion.Calculus.HessianCommutator
import OAI.Geometry.IsometricImmersion.Curvature.GaussConnection
import OAI.Geometry.IsometricImmersion.Energy.HeightEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metric_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p =
      (∑ r, christoffel g r k i p * g p r j) +
        (∑ r, christoffel g r k j p * g p i r) := by
  have hlower (a b c : Fin 2) :
      (∑ r, christoffel g r a b p * g p c r) = christoffelFirstKind g a b p c := by
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using
      congrFun (metric_mul_christoffel hg hp a b) c
  have hsym : (∑ r, christoffel g r k i p * g p r j) =
      ∑ r, christoffel g r k i p * g p j r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [metric_coeff_symm hg hp r j]
  rw [hsym, hlower k i j, hlower k j i]
  simp only [christoffelFirstKind]
  rw [metric_coeff_partial_symm hg hU hp k j i]
  ring

theorem metricDet_coordPartial (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (fun q => (g q).det) p =
      coordPartial k (fun q => g q 0 0) p * g p 1 1 +
        g p 0 0 * coordPartial k (fun q => g q 1 1) p -
        (coordPartial k (fun q => g q 0 1) p * g p 1 0 +
          g p 0 1 * coordPartial k (fun q => g q 1 0) p) := by
  have hd (i j : Fin 2) : DifferentiableAt ℝ (fun q => g q i j) p :=
    (((hg.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [Matrix.det_fin_two]
  have hprod₀ : DifferentiableAt ℝ (fun q => g q 0 0 * g q 1 1) p :=
    (hd 0 0).mul (hd 1 1)
  have hprod₁ : DifferentiableAt ℝ (fun q => g q 0 1 * g q 1 0) p :=
    (hd 0 1).mul (hd 1 0)
  rw [HessianCalculus.coordPartial_sub_at hprod₀ hprod₁ k,
    HessianCalculus.coordPartial_mul_at (hd 0 0) (hd 1 1) k,
    HessianCalculus.coordPartial_mul_at (hd 0 1) (hd 1 0) k]

theorem metricDet_partial_trace (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (fun q => (g q).det) p =
      2 * (christoffel g 0 k 0 p + christoffel g 1 k 1 p) * (g p).det := by
  rw [metricDet_coordPartial hg hU hp k]
  simp only [metric_compatibility hg hU hp, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem metricDet_partial_y (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) :
    coordPartial 1 (fun q => (g q).det) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * (g p).det := by
  rw [metricDet_partial_trace hg hU hp 1,
    christoffel_lower_symm hg hU hp 0 1 0]

theorem heightEnergy_polynomial_symm (z : Coord → ℝ)
    (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    heightEnergy g z p = (g p).det -
      (g p 1 1 * (coordPartial 0 z p) ^ 2 -
        2 * g p 0 1 * coordPartial 0 z p * coordPartial 1 z p +
        g p 0 0 * (coordPartial 1 z p) ^ 2) := by
  rw [heightEnergy_polynomial z hg hp, metric_coeff_symm hg hp 1 0]
  ring

namespace CompatibilityCalculus

theorem coordPartial_quadratic
    {A B C X Y : Coord → ℝ} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hX : DifferentiableAt ℝ X p)
    (hY : DifferentiableAt ℝ Y p) (k : Fin 2) :
    coordPartial k (fun q => A q * (X q) ^ 2 -
      2 * B q * X q * Y q + C q * (Y q) ^ 2) p =
      coordPartial k A p * (X p) ^ 2 + 2 * A p * X p * coordPartial k X p -
        (2 * coordPartial k B p * X p * Y p +
          2 * B p * coordPartial k X p * Y p +
          2 * B p * X p * coordPartial k Y p) +
        coordPartial k C p * (Y p) ^ 2 + 2 * C p * Y p * coordPartial k Y p := by
  have hd := ((hA.hasFDerivAt.fun_mul (hX.hasFDerivAt.fun_mul hX.hasFDerivAt)).sub
    (((hB.hasFDerivAt.const_mul (2 : ℝ)).fun_mul hX.hasFDerivAt).fun_mul hY.hasFDerivAt)).add
      (hC.hasFDerivAt.fun_mul (hY.hasFDerivAt.fun_mul hY.hasFDerivAt))
  simp only [Pi.add_def, Pi.sub_def] at hd
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

end CompatibilityCalculus

theorem coordPartial_heightEnergy_polynomial
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (heightEnergy g z) p =
      coordPartial k (fun q => (g q).det) p -
        (coordPartial k (fun q => g q 1 1) p * (coordPartial 0 z p) ^ 2 +
          2 * g p 1 1 * coordPartial 0 z p * coordPartial k (coordPartial 0 z) p -
          (2 * coordPartial k (fun q => g q 0 1) p * coordPartial 0 z p * coordPartial 1 z p +
            2 * g p 0 1 * coordPartial k (coordPartial 0 z) p * coordPartial 1 z p +
            2 * g p 0 1 * coordPartial 0 z p * coordPartial k (coordPartial 1 z) p) +
          coordPartial k (fun q => g q 0 0) p * (coordPartial 1 z p) ^ 2 +
          2 * g p 0 0 * coordPartial 1 z p * coordPartial k (coordPartial 1 z) p) := by
  have heq : heightEnergy g z =ᶠ[𝓝 p] (fun q => (g q).det -
      (g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact heightEnergy_polynomial_symm z hg hq
  have hdg (i j : Fin 2) : DifferentiableAt ℝ (fun q => g q i j) p :=
    (((hg.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdz (i : Fin 2) : DifferentiableAt ℝ (coordPartial i z) p :=
    (((partial_contDiffOn hz hU i) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdet : DifferentiableAt ℝ (fun q => (g q).det) p :=
    (((metricDet_contDiffOn hg) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hquad : DifferentiableAt ℝ (fun q =>
      g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2) p :=
    (((hdg 1 1).mul ((hdz 0).pow 2)).sub
      ((((hdg 0 1).const_mul (2 : ℝ)).mul (hdz 0)).mul (hdz 1))).add
        ((hdg 0 0).mul ((hdz 1).pow 2))
  change fderiv ℝ (heightEnergy g z) p (Pi.single k 1) = _
  rw [heq.fderiv_eq]
  change coordPartial k (fun q => (g q).det -
      (g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2)) p = _
  rw [HessianCalculus.coordPartial_sub_at hdet hquad k,
    CompatibilityCalculus.coordPartial_quadratic
      (hdg 1 1) (hdg 0 1) (hdg 0 0) (hdz 0) (hdz 1) k]

theorem coordPartial_heightEnergy
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (heightEnergy g z) p =
      2 * (christoffel g 0 k 0 p + christoffel g 1 k 1 p) * heightEnergy g z p -
        2 * (covHessian g z p k 0 *
            (g p 1 1 * coordPartial 0 z p - g p 0 1 * coordPartial 1 z p) +
          covHessian g z p k 1 *
            (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p)) := by
  rw [coordPartial_heightEnergy_polynomial hg hU hz hp k,
    metricDet_partial_trace hg hU hp k, heightEnergy_polynomial_symm z hg hp]
  simp only [metric_compatibility hg hU hp, covHessian, Fin.sum_univ_two,
    Matrix.det_fin_two]
  rw [metric_coeff_symm hg hp 1 0]
  ring

theorem heightEnergy_y_quotient
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    coordPartial 1 (heightEnergy g z) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * heightEnergy g z p -
        2 * covHessian g z p 1 1 *
          ((g p 0 0 - (covHessian g z p 0 1 / covHessian g z p 1 1) * g p 0 1) *
              coordPartial 1 z p -
            (g p 0 1 - (covHessian g z p 0 1 / covHessian g z p 1 1) * g p 1 1) *
              coordPartial 0 z p) := by
  rw [coordPartial_heightEnergy hg hU hz hp 1,
    christoffel_lower_symm hg hU hp 0 1 0,
    covHessian_symm hg hU hz hp 1 0]
  field_simp [hyy]
  ring

end SmoothLocal.Geometry

end

end OAI
