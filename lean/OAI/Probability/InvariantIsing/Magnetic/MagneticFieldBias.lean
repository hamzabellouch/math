import OAI.Probability.InvariantIsing.Fields.FieldHeightChart
import OAI.Probability.InvariantIsing.Fields.FieldScalarDerivative

namespace OAI

/-! The physical mean spin is the bias derivative of the actual finite
field functional, including its zero-exponent root Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- The mean spin before the root increment, at an arbitrary bias. -/
def fieldBiasMean (h : FieldStep) : ℝ → ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarMean (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh)

lemma fieldValue_root (h : FieldStep) (b : ℝ) :
    fieldValue h b =
      gaussianOperator 0 (h.height 0)
        (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b -
      h.height (Fin.last h.depth) / 2 := by
  rw [← fieldAllIncrements_value h b, fieldAllIncrements_root]
  rfl

lemma fieldBiasMean_regular (h : FieldStep) :
    Measurable (fieldBiasMean h) ∧ ∀ b, |fieldBiasMean h b| ≤ 1 := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hD := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  exact ⟨measurable_fieldSpinTransition 0 _ hF.1 hD.1,
    fieldSpinTransition_bound 0 _ hF.1 hF.2 hD.2⟩

lemma hasDerivAt_fieldValue_bias (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldValue h) (fieldBiasMean h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hD := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  have hd := hasDerivAt_gaussianOperator 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hF.1 hF.2 hD.1 zero_le_one hD.2
    (hasDerivAt_fieldScalarLogCosh (scalarFieldIncrements h) hL) b
  convert hd.sub_const (h.height (Fin.last h.depth) / 2) using 1
  · funext z
    exact fieldValue_root h z
  · rfl

lemma continuous_fieldValue_bias (h : FieldStep) : Continuous (fieldValue h) :=
  continuous_iff_continuousAt.mpr fun b => (hasDerivAt_fieldValue_bias h b).continuousAt

end InvariantIsing

end

end OAI
