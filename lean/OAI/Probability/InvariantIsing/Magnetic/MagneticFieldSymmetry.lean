import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverse
import OAI.Probability.InvariantIsing.Fields.FieldScalarOrder

namespace OAI

/-! Spin-flip symmetry of the actual bias optimization and recovery of
the zero-magnetization scalar field functional. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldValue_bias_even (h : FieldStep) : Function.Even (fieldValue h) := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have he := fieldScalarValue_even (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth (fun z => by simp only [Real.cosh_neg])
  have hr := gaussianOperator_even 0 (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 he
  intro b
  rw [fieldValue_root, fieldValue_root]
  exact congrArg (fun x => x - h.height (Fin.last h.depth) / 2) (hr b)

lemma fieldBiasMean_zero (h : FieldStep) : fieldBiasMean h 0 = 0 := by
  have hp := hasDerivAt_fieldValue_bias h 0
  have hp' : HasDerivAt (fieldValue h) (fieldBiasMean h 0) (-0) := by simpa using hp
  have hn := hp'.comp 0 (hasDerivAt_neg (0 : ℝ))
  have hn' : HasDerivAt (fieldValue h) (-fieldBiasMean h 0) 0 := by
    convert hn using 1
    · funext b
      exact (fieldValue_bias_even h b).symm
    · ring
  linarith [hp.unique hn']

@[simp] lemma magneticBias_zero (h : FieldStep) : magneticBias h 0 = 0 := by
  apply (strictMono_fieldBiasMean h).injective
  rw [fieldBiasMean_magneticBias h (by norm_num), fieldBiasMean_zero]

@[simp] lemma constrainedFieldValue_zero_magnetization (h : FieldStep) :
    constrainedFieldValue h 0 = fieldValue h 0 := by
  rw [constrainedFieldValue_magneticBias h (by norm_num), magneticBias_zero]
  simp only [mul_zero, sub_zero]

lemma magneticBiasObjective_reflect (h : FieldStep) (s b : ℝ) :
    magneticBiasObjective h (-s) (-b) = magneticBiasObjective h s b := by
  unfold magneticBiasObjective
  rw [fieldValue_bias_even h b]
  ring

lemma constrainedFieldValue_even (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    constrainedFieldValue h (-s) = constrainedFieldValue h s := by
  obtain ⟨b, hb⟩ := exists_magneticBias_minimum h hs
  have hbr : ∀ c, magneticBiasObjective h (-s) (-b) ≤ magneticBiasObjective h (-s) c := by
    intro c
    have hh := hb (-c)
    rw [magneticBiasObjective_reflect]
    convert hh using 1
    rw [← magneticBiasObjective_reflect h s (-c)]
    simp only [neg_neg]
  rw [constrainedFieldValue_eq_at_minimum h hbr,
    constrainedFieldValue_eq_at_minimum h hb, magneticBiasObjective_reflect]

lemma magneticBias_odd (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    magneticBias h (-s) = -magneticBias h s := by
  have hs' : |-s| < 1 := by simpa only [abs_neg] using hs
  apply magneticBias_minimum_unique h (magneticBias_minimizes h hs')
  intro c
  have hh := magneticBias_minimizes h hs (-c)
  rw [magneticBiasObjective_reflect]
  convert hh using 1
  rw [← magneticBiasObjective_reflect h s (-c)]
  simp only [neg_neg]

end InvariantIsing

end

end OAI
