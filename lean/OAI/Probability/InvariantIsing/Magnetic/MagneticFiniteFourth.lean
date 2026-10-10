import OAI.Probability.InvariantIsing.Magnetic.MagneticRelativeFourth

namespace OAI

/-! Relative fourth derivatives for the actual finite Ising field recursion,
and the bounded coefficients needed for inverse-coordinate comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticFourthRatioCap : List (ℝ × ℝ≥0) → ℝ
  | [] => 6
  | av :: L => magneticFourthRatioCap L + 8 * |av.1| * magneticThirdRatioCap L +
      3 * |av.1| + 37 * av.1 ^ 2

lemma magneticFourthRatioCap_nonneg (L : List (ℝ × ℝ≥0)) :
    0 ≤ magneticFourthRatioCap L := by
  induction L with
  | nil => norm_num [magneticFourthRatioCap]
  | cons av L ih =>
    change 0 ≤ magneticFourthRatioCap L + 8 * |av.1| * magneticThirdRatioCap L +
      3 * |av.1| + 37 * av.1 ^ 2
    have ht := magneticThirdRatioCap_nonneg L
    positivity

lemma field_logCosh_fourth_relative (z : ℝ) :
    |fieldLogCoshFourth z| ≤ 6 * (1 / (Real.cosh z) ^ 2) := by
  let q := 1 / (Real.cosh z) ^ 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q ≤ 1 := (le_abs_self q).trans (field_tanh_second_bound z)
  have hm2 : (Real.tanh z) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (field_abs_tanh_le_one z) 2
    simpa only [sq_abs, one_pow] using h
  change |-2 * q ^ 2 + 4 * (Real.tanh z) ^ 2 * q| ≤ 6 * q
  have h1 : |-2 * q ^ 2| ≤ 2 * q := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg q)]
    nlinarith
  have h2 : |4 * (Real.tanh z) ^ 2 * q| ≤ 4 * q := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hm2)]
  exact (abs_add_le _ _).trans (by linarith)

theorem fieldScalarLogCoshFourth_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    |fieldScalarFourth L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2)
        (fun x => -2 * Real.tanh x / (Real.cosh x) ^ 2) fieldLogCoshFourth z| ≤
      magneticFourthRatioCap L * fieldScalarSecond L
        (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact field_logCosh_fourth_relative z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hr := fieldScalarThird_regular L ht measurable_logCosh logCosh_linearGrowth
      hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
      field_tanh_second_bound field_logCosh_third_bound
    have hterminal : Measurable fieldLogCoshFourth := by
      unfold fieldLogCoshFourth
      fun_prop
    have hs := fieldScalarFourth_regular L ht measurable_logCosh logCosh_linearGrowth
      hm (by fun_prop) (by fun_prop) hterminal zero_le_one field_abs_tanh_le_one
      field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
    have hq1 (x : ℝ) : fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) x ≤ 1 := by
      have hh := fieldScalarLogCoshSecond_le_spin_variance L ht htζ x
      linarith [sq_nonneg (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh x)]
    have hp := (hL av List.mem_cons_self).le
    have he := fieldFourthTransform_relative_bound hp av.2 hv.1 hv.2 ha.1 hq.1 hr.1 hs.1
      ha.2 (fun x => (fieldScalarLogCoshSecond_pos L ht x).le) hq1
      (magneticThirdRatioCap_nonneg L) (magneticFourthRatioCap_nonneg L)
      (fieldScalarLogCoshThird_relative L ht) (ih ht htζ) z
    simpa only [fieldScalarFourth, fieldScalarSecond, fieldScalarMean, magneticFourthRatioCap,
      abs_of_nonneg hp, fieldCurvatureTransform] using he

lemma fieldBiasFourth_relative (h : FieldStep) (b : ℝ) :
    |fieldBiasFourth h b| ≤ magneticFourthRatioCap (scalarFieldIncrements h) *
      fieldBiasCurvature h b := by
  have hL := scalarFieldIncrements_positive h
  have hζ : ∀ av ∈ scalarFieldIncrements h, av.1 ≤ 1 := by
    intro av hav
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
    change h.cut i.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hv := fieldScalarValue_regular _ hL measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have ha := fieldScalarMean_regular _ hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hq := fieldScalarLogCoshSecond_regular _ hL
  have hr := fieldScalarThird_regular _ hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound
  have hterminal : Measurable fieldLogCoshFourth := by unfold fieldLogCoshFourth; fun_prop
  have hs := fieldScalarFourth_regular _ hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) hterminal zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
  have hq1 (x : ℝ) : fieldScalarSecond (scalarFieldIncrements h)
      (fun x => Real.log (Real.cosh x)) Real.tanh (fun x => 1 / (Real.cosh x) ^ 2) x ≤ 1 := by
    have hh := fieldScalarLogCoshSecond_le_spin_variance _ hL hζ x
    linarith [sq_nonneg (fieldScalarMean (scalarFieldIncrements h)
      (fun x => Real.log (Real.cosh x)) Real.tanh x)]
  have he := fieldFourthTransform_relative_bound (by norm_num : (0 : ℝ) ≤ 0)
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 ha.1 hq.1 hr.1 hs.1 ha.2
    (fun x => (fieldScalarLogCoshSecond_pos _ hL x).le) hq1
    (magneticThirdRatioCap_nonneg _) (magneticFourthRatioCap_nonneg _)
    (fieldScalarLogCoshThird_relative _ hL) (fieldScalarLogCoshFourth_relative _ hL hζ) b
  simpa only [fieldFourthTransform, fieldTiltSpatial, fieldThirdTransform,
    fieldCurvatureTransform, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero, fieldBiasFourth, fieldBiasCurvature] using he

end InvariantIsing

end

end OAI
