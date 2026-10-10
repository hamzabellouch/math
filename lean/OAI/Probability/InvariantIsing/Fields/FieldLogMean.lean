import OAI.Probability.InvariantIsing.Fields.FieldLogNormalizer
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteFieldVariance
import OAI.Probability.InvariantIsing.Cavity.CavityScalarRoot

namespace OAI

/-! The log normalizer has the manuscript's scalar field value, with
its terminal covariance subtraction restored before taking the mean. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepVariance_eq_fieldCascadeVariance (h : FieldStep) :
    fieldStepVariance h = fieldCascadeVariance h := by
  funext i
  apply NNReal.eq
  change (fieldStepVariance h i : ℝ) = (pathAmplitude (heightSequence h) (i + 1))^2
  rw [pathAmplitude_sq (heightSequence_mono h) (heightSequence_nonneg h 0), pathIncrement]
  by_cases hi : i < h.depth
  · rw [fieldStepVariance_eq_height_sub h ⟨i, hi⟩,
      heightSequence_eq h (i + 1) (by omega), heightSequence_eq h i (by omega)]
    rfl
  · have hle : h.depth ≤ i := Nat.le_of_not_gt hi
    simp only [fieldStepVariance, dite_eq_right hi, NNReal.coe_zero, heightSequence,
      min_eq_right hle, min_eq_right (hle.trans (Nat.le_succ i)), sub_self]

theorem field_vector_log_mean (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (U : Rotation N) :
    let μ := (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) :
      Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)
    Integrable (fun p => fieldVectorLogNormalizer N h p.1 p.2) μ ∧
      (N : ℝ)⁻¹ * (∫ p, fieldVectorLogNormalizer N h p.1 p.2 ∂μ) =
        fieldValue h 0 + h.height (Fin.last h.depth) / 2 := by
  intro μ
  have hc := field_vector_log_root_integral N hN h
    (NNReal.mk (h.height 0) (h.nonneg 0))
  refine ⟨hc.1, ?_⟩
  rw [hc.2, fieldStepVariance_eq_fieldCascadeVariance]
  have he := cavityScalarCascadeMean_fieldStep N hN h 0 0 U
  have hterm : cavityResidualSpinLog N 0 0 =
      (fun y => ∑ i, Real.log (Real.cosh (y i))) := by
    funext y
    simp only [cavityResidualSpinLog_eq, NNReal.coe_zero, add_zero, mul_zero,
      zero_div, zero_add]
  simpa only [cavityScalarCascadeMean, hterm, NNReal.coe_zero, add_zero, zero_div] using he

end InvariantIsing

end

end OAI
