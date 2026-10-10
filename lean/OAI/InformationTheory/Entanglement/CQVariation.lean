import OAI.InformationTheory.Entanglement.TraceMatrixSpace
import OAI.InformationTheory.Entanglement.MatrixMeasureChannel

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory Matrix.Norms.L2Operator
open MeasureTheory Matrix
namespace SecretKey
open ChannelCompletion
variable {T : Type*} [MeasurableSpace T] {n : Type} [Fintype n] [DecidableEq n]

def traceDensityMeasure (μ : Measure T) (D : T → Mat n) : VectorMeasure T (TraceMatrix n) :=
  μ.withDensityᵥ (fun t => TraceMatrix.mk (D t))
lemma traceDensityMeasure_value (μ : Measure T) (D : T → Mat n)
    (hi : ∀ a b, Integrable (fun t => D t a b) μ) {s : Set T} (hs : MeasurableSet s) :
    (traceDensityMeasure μ D s).val=fun a b => ∫ t in s, D t a b ∂μ := by
  rw [traceDensityMeasure,withDensityᵥ_apply (TraceMatrix.integrable_into hi) hs]
  ext a b
  exact TraceMatrix.setIntegral_entry hi s a b
lemma traceDensityMeasure_variation (μ : Measure T) (D : T → Mat n)
    (hi : ∀ a b, Integrable (fun t => D t a b) μ) :
    (traceDensityMeasure μ D).variation Set.univ=ENNReal.ofReal (∫ t, traceNorm (D t) ∂μ) := by
  rw [traceDensityMeasure,Measure.variation_withDensityᵥ (TraceMatrix.integrable_into hi),
    withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  simp only [← ofReal_norm]
  rw [← ofReal_integral_eq_lintegral_ofReal (TraceMatrix.integrable_into hi).norm
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))]
  rfl
omit [Fintype n] [DecidableEq n] in
lemma idealDensity_entry_integrable (σ : T → Mat n) {μ : Measure T}
    (hi : ∀ a b, Integrable (fun t => σ t a b) μ) (i j : Fin 2) (a b : n) :
    Integrable (fun t => idealDensity σ i j t a b) μ := by
  unfold idealDensity halfDensity
  split_ifs
  · exact (hi a b).const_mul _
  · exact integrable_zero _ _ _
omit [Fintype n] [DecidableEq n] in
lemma idealDensity_entry_integral (σ : T → Mat n) {μ : Measure T}
    (s : Set T) (i j : Fin 2) (a b : n) :
    (∫ t in s, idealDensity σ i j t a b ∂μ)=
      (if i=j then (1/2 : ℂ)*(∫ t in s, σ t a b ∂μ) else 0) := by
  unfold idealDensity halfDensity
  split_ifs <;> simp only [Matrix.smul_apply,smul_eq_mul,integral_const_mul,Matrix.zero_apply,integral_zero]
def cqDifferenceMeasure (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) (i j : Fin 2) : VectorMeasure T (TraceMatrix n) :=
  traceDensityMeasure (bitComparisonMeasure W σ) (fun t =>
    (W i j).positiveDensity (bitComparisonMeasure W σ) t-
      idealDensity (σ.positiveDensity (bitComparisonMeasure W σ)) i j t)
lemma cqDifferenceMeasure_value (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) (i j : Fin 2) {s : Set T} (hs : MeasurableSet s) :
    (cqDifferenceMeasure W σ i j s).val=
      (W i j).value s-(if i=j then halfDensity (σ.value s) else 0) := by
  rw [cqDifferenceMeasure]
  rw [traceDensityMeasure_value _ (fun t => (W i j).positiveDensity (bitComparisonMeasure W σ) t-
      idealDensity (σ.positiveDensity (bitComparisonMeasure W σ)) i j t) (fun a b =>
    ((W i j).positiveDensity_integrable (bitComparison_actual_dom W σ i j) a b).sub
      (idealDensity_entry_integrable _ (σ.positiveDensity_integrable (bitComparison_ideal_dom W σ)) i j a b)) hs]
  ext a b
  simp only [Matrix.sub_apply]
  rw [integral_sub
    ((W i j).positiveDensity_integrable (bitComparison_actual_dom W σ i j) a b).integrableOn
    (idealDensity_entry_integrable _ (σ.positiveDensity_integrable (bitComparison_ideal_dom W σ)) i j a b).integrableOn,
    (W i j).positiveDensity_setIntegral (bitComparison_actual_dom W σ i j) hs,
    idealDensity_entry_integral,σ.positiveDensity_setIntegral (bitComparison_ideal_dom W σ) hs]
  split_ifs <;> rfl

theorem cqBitDistance_variation (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) :
    ENNReal.ofReal (cqBitDistance W σ)=
      ∑ i, ∑ j, (cqDifferenceMeasure W σ i j).variation Set.univ := by
  unfold cqBitDistance bitDistance
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => integral_nonneg (fun t => traceNorm_nonneg _)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg (fun t => traceNorm_nonneg _))]
  apply Finset.sum_congr rfl
  intro j _
  exact (traceDensityMeasure_variation _ _ (fun a b =>
    ((W i j).positiveDensity_integrable (bitComparison_actual_dom W σ i j) a b).sub
      (idealDensity_entry_integrable _ (σ.positiveDensity_integrable (bitComparison_ideal_dom W σ)) i j a b))).symm

end SecretKey

end

end OAI
