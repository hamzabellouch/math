import Mathlib
import OAI.Geometry.SmoothYau.Model

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

def chartTransition (p q : M) : E → E := (chartAt E p) ∘ (chartAt E q).symm

def coordinateTransitionMatrix (p q : M) (y : E) :
    Matrix (CoordIndex E) (CoordIndex E) ℝ :=
  LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
    (fderiv ℝ (chartTransition p q) y).toLinearMap

def inverseChartDerivative (p : M) (y : E) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y

omit [FiniteDimensional ℝ E] in
lemma invChart_derivative_change (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (inverseChartDerivative p (chartTransition p q y)).comp
      (fderiv ℝ (chartTransition p q) y) =
      inverseChartDerivative q y := by
  have hpc := mdifferentiable_chart (I := 𝓘(ℝ, E)) p
  have hqc := mdifferentiable_chart (I := 𝓘(ℝ, E)) q
  have hc := mfderiv_comp y (hpc.mdifferentiableAt hp) (hqc.mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at hc
  change fderiv ℝ (chartTransition p q) y = _ at hc
  unfold inverseChartDerivative
  erw [hc, ← ContinuousLinearMap.comp_assoc, hpc.symm_comp_deriv hp,
    ContinuousLinearMap.id_comp]

lemma coordinateVector_change (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source)
    (i : CoordIndex E) :
    coordinateVector q y i = ∑ k, coordinateTransitionMatrix p q y k i •
      coordinateVector p (chartTransition p q y) k := by
  have hh := congrArg (fun L : E →L[ℝ] E => L (Module.finBasis ℝ E i))
    (invChart_derivative_change p q hy hp)
  change _ = coordinateVector q y i at hh
  rw [← hh]
  change (inverseChartDerivative p (chartTransition p q y))
    ((fderiv ℝ (chartTransition p q) y) (Module.finBasis ℝ E i)) = _
  rw [← (Module.finBasis ℝ E).sum_repr ((fderiv ℝ (chartTransition p q) y) (Module.finBasis ℝ E i))]
  simp only [map_sum, map_smul, coordinateTransitionMatrix, LinearMap.toMatrix_apply]
  rfl

omit [FiniteDimensional ℝ E] in
private lemma bilinear_sum_matrix {ι : Type*} [Fintype ι]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : ι → ι → ℝ) (v : ι → E) (i j : ι) :
    B (∑ k, a k i • v k) (∑ k, a k j • v k) =
      ∑ k, ∑ l, a l i * B (v l) (v k) * a k j := by
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma metricCoefficients_change (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    metricCoefficients g q y = (coordinateTransitionMatrix p q y).transpose *
      metricCoefficients g p (chartTransition p q y) * coordinateTransitionMatrix p q y := by
  ext i j
  have he : (chartAt E p).symm (chartTransition p q y) = (chartAt E q).symm y :=
    (chartAt E p).left_inv hp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, metricCoefficients, Finset.sum_mul]
  rw [he]
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E q).symm y)
  change B (coordinateVector q y i) (coordinateVector q y j) = _
  rw [coordinateVector_change p q hy hp i, coordinateVector_change p q hy hp j]
  change B (∑ k : CoordIndex E, coordinateTransitionMatrix p q y k i •
    (coordinateVector p (chartTransition p q y) k : E))
    (∑ k : CoordIndex E, coordinateTransitionMatrix p q y k j •
    (coordinateVector p (chartTransition p q y) k : E)) = _
  exact bilinear_sum_matrix B (coordinateTransitionMatrix p q y)
    (fun k => (coordinateVector p (chartTransition p q y) k : E)) i j
end YauCounterexamples

end

end OAI
