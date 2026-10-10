import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarFourth
import OAI.Probability.InvariantIsing.Magnetic.MagneticInverseVariation
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverse

namespace OAI

/-! First and second spatial derivatives of the actual curvature in
the physical mean-spin coordinate. The root exponent remains zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma magnetic_tanh_measurable : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp only [Real.tanh_eq]
  fun_prop

private lemma magnetic_third_terminal_measurable :
    Measurable (fun z : ℝ => -2 * Real.tanh z / (Real.cosh z) ^ 2) := by
  have hm := magnetic_tanh_measurable
  fun_prop

private lemma magnetic_tail_third_regular (h : FieldStep) :
    Measurable (fieldScalarThird (scalarFieldIncrements h)
      (fun z => Real.log (Real.cosh z)) Real.tanh (fun z => 1 / (Real.cosh z) ^ 2)
      (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2)) ∧
    ∀ z, |fieldScalarThird (scalarFieldIncrements h)
      (fun z => Real.log (Real.cosh z)) Real.tanh (fun z => 1 / (Real.cosh z) ^ 2)
      (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2) z| ≤
        fieldScalarThirdCap (scalarFieldIncrements h) 1 1 2 :=
  fieldScalarThird_regular _ (scalarFieldIncrements_positive h) measurable_logCosh
    logCosh_linearGrowth magnetic_tanh_measurable (by fun_prop) magnetic_third_terminal_measurable
    zero_le_one field_abs_tanh_le_one field_tanh_second_bound field_logCosh_third_bound

private lemma magnetic_tail_fourth_regular (h : FieldStep) :
    Measurable (fieldScalarFourth (scalarFieldIncrements h)
      (fun z => Real.log (Real.cosh z)) Real.tanh (fun z => 1 / (Real.cosh z) ^ 2)
      (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2) fieldLogCoshFourth) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |fieldScalarFourth (scalarFieldIncrements h)
      (fun z => Real.log (Real.cosh z)) Real.tanh (fun z => 1 / (Real.cosh z) ^ 2)
      (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2) fieldLogCoshFourth z| ≤ B := by
  have hf : Measurable fieldLogCoshFourth := by
    have hm := magnetic_tanh_measurable
    unfold fieldLogCoshFourth
    fun_prop
  exact fieldScalarFourth_regular _ (scalarFieldIncrements_positive h) measurable_logCosh
    logCosh_linearGrowth magnetic_tanh_measurable (by fun_prop) magnetic_third_terminal_measurable hf
    zero_le_one field_abs_tanh_le_one field_tanh_second_bound field_logCosh_third_bound
    field_logCosh_fourth_bound

def fieldBiasThird (h : FieldStep) : ℝ → ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarThird (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (fun z => 1 / (Real.cosh z) ^ 2)
      (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2))

def fieldBiasFourth (h : FieldStep) : ℝ → ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarFourth (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (fun z => 1 / (Real.cosh z) ^ 2)
      (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2) fieldLogCoshFourth)

lemma hasDerivAt_fieldBiasCurvature (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldBiasCurvature h) (fieldBiasThird h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular _ hL measurable_logCosh logCosh_linearGrowth
  have hm := fieldScalarMean_regular _ hL measurable_logCosh logCosh_linearGrowth
    magnetic_tanh_measurable field_abs_tanh_le_one
  have hq := fieldScalarLogCoshSecond_regular _ hL
  have hr := magnetic_tail_third_regular h
  have hC : 0 ≤ fieldScalarSecondCap (scalarFieldIncrements h) 1 1 :=
    (abs_nonneg _).trans (hq.2 0)
  have hd := hasDerivAt_fieldSpinTransition 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 hm.1 hq.1 hr.1
    zero_le_one hC hm.2 hq.2 hr.2
    (hasDerivAt_fieldScalarLogCosh _ hL) (hasDerivAt_fieldScalarLogCoshSecond _ hL) b
  simpa only [zero_mul, add_zero, fieldBiasCurvature, fieldBiasThird] using hd

lemma hasDerivAt_fieldBiasThird (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldBiasThird h) (fieldBiasFourth h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular _ hL measurable_logCosh logCosh_linearGrowth
  have hm := fieldScalarMean_regular _ hL measurable_logCosh logCosh_linearGrowth
    magnetic_tanh_measurable field_abs_tanh_le_one
  have hr := magnetic_tail_third_regular h
  obtain ⟨hs, B, hB, bs⟩ := magnetic_tail_fourth_regular h
  have hC : 0 ≤ fieldScalarThirdCap (scalarFieldIncrements h) 1 1 2 :=
    (abs_nonneg _).trans (hr.2 0)
  have hd := hasDerivAt_fieldSpinTransition 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 hm.1 hr.1 hs
    zero_le_one hC hm.2 hr.2 bs
    (hasDerivAt_fieldScalarLogCosh _ hL) (hasDerivAt_fieldScalarLogCoshThird _ hL) b
  simpa only [zero_mul, add_zero, fieldBiasThird, fieldBiasFourth] using hd

def magneticCurvature (h : FieldStep) (s : ℝ) : ℝ :=
  fieldBiasCurvature h (magneticBias h s)

def magneticCurvatureSlope (h : FieldStep) (s : ℝ) : ℝ :=
  fieldBiasThird h (magneticBias h s) / magneticCurvature h s

def magneticCurvatureSecond (h : FieldStep) (s : ℝ) : ℝ :=
  fieldBiasFourth h (magneticBias h s) / (magneticCurvature h s) ^ 2 -
    (fieldBiasThird h (magneticBias h s)) ^ 2 / (magneticCurvature h s) ^ 3

lemma magneticCurvature_pos (h : FieldStep) (s : ℝ) : 0 < magneticCurvature h s :=
  fieldBiasCurvature_pos h _

lemma hasDerivAt_magneticCurvature (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (magneticCurvature h) (magneticCurvatureSlope h s) s := by
  have hb : HasDerivAt (magneticBias h) (1 / magneticCurvature h s) s := by
    simpa only [magneticCurvature, one_div] using hasDerivAt_magneticBias h hs
  have hd := inverse_mean_pullback_derivative hb
    (hasDerivAt_fieldBiasCurvature h (magneticBias h s))
  exact hd

lemma hasDerivAt_magneticCurvatureSlope (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (magneticCurvatureSlope h) (magneticCurvatureSecond h s) s := by
  have hb : HasDerivAt (magneticBias h) (1 / magneticCurvature h s) s := by
    simpa only [magneticCurvature, one_div] using hasDerivAt_magneticBias h hs
  have hd := inverse_mean_pullback_quotient (magneticCurvature_pos h s).ne' hb rfl rfl
    (hasDerivAt_fieldBiasThird h (magneticBias h s))
    (hasDerivAt_fieldBiasCurvature h (magneticBias h s))
  unfold magneticCurvatureSlope magneticCurvatureSecond magneticCurvature
  simpa only [pow_two, magneticCurvature] using hd

lemma hasDerivAt_deriv_magneticCurvature (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (deriv (magneticCurvature h)) (magneticCurvatureSecond h s) s := by
  apply (hasDerivAt_magneticCurvatureSlope h hs).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (hasDerivAt_magneticCurvature h (abs_lt.mpr ht)).deriv

end InvariantIsing

end

end OAI
