import OAI.Probability.InvariantIsing.Magnetic.MagneticSpatialFourth

namespace OAI

/-! The actual fourth spatial derivative through every finite backward
level. Its global bound is finite for each fixed finite field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarFourth : List (ℝ × ℝ≥0) →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, _, _, _, d => d
  | av :: L, F, a, b, c, d => fieldFourthTransform av.1 av.2
      (fieldScalarValue L F) (fieldScalarMean L F a)
      (fieldScalarSecond L F a b) (fieldScalarThird L F a b c)
      (fieldScalarFourth L F a b c d)

lemma fieldScalarFourth_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c d : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    {K C D E : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C)
    (bc : ∀ z, |c z| ≤ D) (bd : ∀ z, |d z| ≤ E) :
    Measurable (fieldScalarFourth L F a b c d) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |fieldScalarFourth L F a b c d z| ≤ B := by
  induction L with
  | nil => exact ⟨hd, E, (abs_nonneg _).trans (bd 0), bd⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := fieldScalarThird_regular L ht hF hG ha hb hc hK ba bb bc
    obtain ⟨hs, B, hB, bs⟩ := ih ht
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    exact ⟨measurable_fieldFourthTransform av.1 av.2 hv.1 hm.1 hq.1 hr.1 hs,
      fieldFourthTransform_bounded av.1 av.2 hv.1 hv.2 hK hC hm.2 hq.2 hr.2 bs⟩

lemma hasDerivAt_fieldScalarThird (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c d : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    {K C D E : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C)
    (bc : ∀ z, |c z| ≤ D) (bd : ∀ z, |d z| ≤ E)
    (dF : ∀ z, HasDerivAt F (a z) z)
    (da : ∀ z, HasDerivAt a (b z) z)
    (db : ∀ z, HasDerivAt b (c z) z)
    (dc : ∀ z, HasDerivAt c (d z) z) (z : ℝ) :
    HasDerivAt (fieldScalarThird L F a b c)
      (fieldScalarFourth L F a b c d z) z := by
  induction L generalizing z with
  | nil => exact dc z
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := fieldScalarThird_regular L ht hF hG ha hb hc hK ba bb bc
    obtain ⟨hs, B, hB, bs⟩ := fieldScalarFourth_regular L ht hF hG ha hb hc hd hK ba bb bc bd
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    have hD : 0 ≤ fieldScalarThirdCap L K C D := (abs_nonneg _).trans (hr.2 0)
    exact hasDerivAt_fieldThirdTransform av.1 av.2 hv.1 hv.2 hm.1 hq.1 hr.1 hs hK hC hD
      hm.2 hq.2 hr.2 bs
      (hasDerivAt_fieldScalarValue L ht hF hG ha hK ba dF)
      (hasDerivAt_fieldScalarMean L ht hF hG ha hb hK ba bb dF da)
      (hasDerivAt_fieldScalarSecond L ht hF hG ha hb hc hK ba bb bc dF da db)
      (ih ht) z

def fieldLogCoshFourth (z : ℝ) : ℝ :=
  -2 * (1 / (Real.cosh z) ^ 2) ^ 2 +
    4 * (Real.tanh z) ^ 2 * (1 / (Real.cosh z) ^ 2)

lemma field_logCosh_fourth_derivative (z : ℝ) :
    HasDerivAt (fun y : ℝ => -2 * Real.tanh y / (Real.cosh y) ^ 2)
      (fieldLogCoshFourth z) z := by
  have hd := ((field_hasDerivAt_tanh z).const_mul (-2)).mul
    (field_logCosh_third_derivative z)
  convert hd using 1
  · funext y
    simp only [Pi.mul_apply, div_eq_mul_inv]
    ring
  · simp only [fieldLogCoshFourth, div_eq_mul_inv]
    ring

lemma field_logCosh_fourth_bound (z : ℝ) : |fieldLogCoshFourth z| ≤ 6 := by
  have ht := field_abs_tanh_le_one z
  have hq := field_tanh_second_bound z
  have ht2 : |(Real.tanh z) ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hq2 : |(1 / (Real.cosh z) ^ 2) ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) hq 2
  unfold fieldLogCoshFourth
  refine (abs_add_le _ _).trans ?_
  have hb1 : |-2 * (1 / (Real.cosh z) ^ 2) ^ 2| ≤ 2 := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hb2 : |4 * (Real.tanh z) ^ 2 * (1 / (Real.cosh z) ^ 2)| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      4 * |Real.tanh z ^ 2| * |1 / Real.cosh z ^ 2| ≤ 4 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht2 (by norm_num)) hq (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  linarith

lemma hasDerivAt_fieldScalarLogCoshThird (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarThird L (fun y => Real.log (Real.cosh y)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2) (fun y => -2 * Real.tanh y / (Real.cosh y) ^ 2))
      (fieldScalarFourth L (fun y => Real.log (Real.cosh y)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2) (fun y => -2 * Real.tanh y / (Real.cosh y) ^ 2)
        fieldLogCoshFourth z) z := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hf : Measurable fieldLogCoshFourth := by
    unfold fieldLogCoshFourth
    fun_prop
  apply hasDerivAt_fieldScalarThird L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) hf zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
  · intro y
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
  · exact field_hasDerivAt_tanh
  · exact field_logCosh_third_derivative
  · exact field_logCosh_fourth_derivative

end InvariantIsing

end

end OAI
