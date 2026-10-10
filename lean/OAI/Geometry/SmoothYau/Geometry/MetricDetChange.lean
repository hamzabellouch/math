import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartTransition
import OAI.Geometry.SmoothYau.Smoothness.SphericalBaseProfileRadius

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricDet_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (metricCoefficients g q y).det = (coordinateTransitionMatrix p q y).det ^ 2 *
      (metricCoefficients g p (chartTransition p q y)).det := by
  rw [metricCoefficients_change g p q hy hp, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

lemma coordinateTransitionMatrix_det_ne_zero (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (coordinateTransitionMatrix p q y).det ≠ 0 := by
  intro h
  have hd := metricDet_change g p q hy hp
  rw [h, zero_pow (by omega), zero_mul] at hd
  exact (metricCoefficients_det_pos g q hy).ne' hd

lemma metricDensity_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    Real.sqrt (metricCoefficients g q y).det = |(coordinateTransitionMatrix p q y).det| *
      Real.sqrt (metricCoefficients g p (chartTransition p q y)).det := by
  rw [metricDet_change g p q hy hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma metricInverse_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    coordinateTransitionMatrix p q y * (metricCoefficients g q y)⁻¹ *
      (coordinateTransitionMatrix p q y).transpose =
        (metricCoefficients g p (chartTransition p q y))⁻¹ := by
  classical
  have hd : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  have ht : IsUnit (coordinateTransitionMatrix p q y).transpose.det := by
    simpa only [Matrix.det_transpose] using hd
  rw [metricCoefficients_change g p q hy hp, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
    Matrix.nonsing_inv_mul_cancel_right _ _ ht]
end YauCounterexamples

end

end OAI
