import OAI.Analysis.LipschitzHilbert.Phase.PredictionNormalization
import OAI.Analysis.LipschitzHilbert.Estimates.NestedAverage

namespace OAI

/-!
# Measurable step-supremum prediction factors

Inside one root cell, a finite measurable partition gives an explicit
step supremum. Logarithmic cell oscillation controls its normalization,
producing the actual nonnegative, measurable, average-one factor.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

/-- A finer cell, restricted to the current root region. -/
def predictionCell (I : Set α) (P : α → κ) (i : κ) : Set α := {x | x ∈ I ∧ P x = i}

/-- Actual cell supremums, constant on the finer partition. -/
def predictionStepSup (B : α → ℝ) (I : Set α) (P : α → κ) (x : α) : ℝ :=
  predictionCellSup B (predictionCell I P (P x))

omit [MeasurableSpace α] [Fintype κ] in
theorem predictionStepSup_constant (B : α → ℝ) (I : Set α) (P : α → κ)
    {x y : α} (hxy : P x = P y) : predictionStepSup B I P x = predictionStepSup B I P y := by
  simp only [predictionStepSup, hxy]

theorem measurable_finite_profile (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    Measurable (fun x => c (P x)) := by
  classical
  have heq : (fun x => c (P x)) =
      fun x => ∑ i, ({y | P y = i}.indicator (fun _ => c i)) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      exact Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm) _
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hP i)

theorem measurable_predictionStepSup (B : α → ℝ) (I : Set α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) : Measurable (predictionStepSup B I P) :=
  measurable_finite_profile P hP (fun i => predictionCellSup B (predictionCell I P i))

theorem integrable_predictionStepSup (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → ℝ) (I : Set α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) : Integrable (predictionStepSup B I P) μ :=
  integrable_finite_profile μ P hP (fun i => predictionCellSup B (predictionCell I P i))

omit [MeasurableSpace α] [Fintype κ] in
theorem predictionStepSup_bounds (B : α → ℝ) (I : Set α) (P : α → κ)
    (hpositive : ∀ x ∈ I, 0 < B x) {c : ℝ}
    (hosc : ∀ x ∈ I, ∀ y ∈ I, P y = P x → |Real.log (B y) - Real.log (B x)| ≤ c)
    {x : α} (hx : x ∈ I) :
    B x ≤ predictionStepSup B I P x ∧ predictionStepSup B I P x ≤ Real.exp c * B x := by
  exact prediction_cell_sup_bounds B (predictionCell I P (P x)) ⟨hx, rfl⟩
    (fun y hy => hpositive y hy.1) (fun y hy => hosc x hx y hy.1 hy.2)

omit [MeasurableSpace α] [Fintype κ] in
theorem predictionStepSup_nonnegative (B : α → ℝ) (I : Set α) (P : α → κ)
    (hpositive : ∀ x ∈ I, 0 < B x) {c : ℝ}
    (hosc : ∀ x ∈ I, ∀ y ∈ I, P y = P x → |Real.log (B y) - Real.log (B x)| ≤ c)
    (x : α) : 0 ≤ predictionStepSup B I P x := by
  classical
  by_cases hcell : ∃ y, y ∈ I ∧ P y = P x
  · obtain ⟨y, hy, hxy⟩ := hcell
    rw [← predictionStepSup_constant B I P hxy]
    exact (hpositive y hy).le.trans (predictionStepSup_bounds B I P hpositive hosc hy).1
  · have he : predictionCell I P (P x) = ∅ := by
      ext y
      simp only [predictionCell, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hxy
      exact hcell ⟨y, hy, hxy⟩
    simp [predictionStepSup, he, predictionCellSup]

/-- Construct the normalized step factor explicitly, including measurability,
constancy on finer cells, integral at most one, and the pointwise comparison. -/
theorem exists_normalized_prediction_steps (μ : Measure α) [IsProbabilityMeasure μ]
    (B : α → ℝ) (I : Set α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (hsupport : ∀ᵐ x ∂μ, x ∈ I)
    (hpositive : ∀ x ∈ I, 0 < B x) (hB : Integrable B μ)
    {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (haverage : ∫ x, B x ∂μ ≤ 1 + a * u)
    (hosc : ∀ x ∈ I, ∀ y ∈ I, P y = P x → |Real.log (B y) - Real.log (B x)| ≤ b * u) :
    ∃ Γ : α → ℝ, Measurable Γ ∧ Integrable Γ μ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∫ x, Γ x ∂μ) ≤ 1 ∧ (∀ x y, P x = P y → Γ x = Γ y) ∧
      ∀ x ∈ I, B x ≤ Real.exp ((a + b) * u) * Γ x := by
  let S := predictionStepSup B I P
  let Γ := normalizedPrediction μ S
  have hS : Integrable S μ := integrable_predictionStepSup μ B I P hP
  have hS0 : ∀ x, 0 ≤ S x := predictionStepSup_nonnegative B I P hpositive hosc
  have hmajorant : ∀ᵐ x ∂μ, S x ≤ Real.exp (b * u) * B x := by
    filter_upwards [hsupport] with x hx
    exact (predictionStepSup_bounds B I P hpositive hosc hx).2
  have hcost := step_normalization_cost μ B S ha hb hu hB hS hmajorant haverage
  have hnorm := predictionNormalizer_pos μ S
  refine ⟨Γ, ?_, ?_, ?_, normalizedPrediction_average_le_one μ S, ?_, ?_⟩
  · exact (measurable_predictionStepSup B I P hP).div_const _
  · exact hS.div_const _
  · exact normalizedPrediction_nonnegative μ S hS0
  · intro x y hxy
    unfold Γ normalizedPrediction
    exact congrArg (fun z : ℝ => z / predictionNormalizer μ S)
      (predictionStepSup_constant B I P hxy)
  · intro x hx
    have hm : predictionNormalizer μ S ≤ Real.exp ((a + b) * u) :=
      (Real.log_le_iff_le_exp hnorm).mp hcost
    have hrestore : S x = predictionNormalizer μ S * Γ x := by
      dsimp [Γ, normalizedPrediction]
      field_simp
    calc
      B x ≤ S x := (predictionStepSup_bounds B I P hpositive hosc hx).1
      _ = predictionNormalizer μ S * Γ x := hrestore
      _ ≤ Real.exp ((a + b) * u) * Γ x :=
        mul_le_mul_of_nonneg_right hm (normalizedPrediction_nonnegative μ S hS0 x)

end LipschitzHilbert

end

end OAI
