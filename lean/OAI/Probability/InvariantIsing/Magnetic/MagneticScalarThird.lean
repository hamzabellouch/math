import OAI.Probability.InvariantIsing.Magnetic.MagneticSpatialThird

namespace OAI

/-! The third spatial derivative propagated through the finite scalar
recursion, with an explicit finite bound at every level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarThird : List (ℝ × ℝ≥0) →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, _, _, c => c
  | av :: L, F, a, b, c => fieldThirdTransform av.1 av.2
      (fieldScalarValue L F) (fieldScalarMean L F a)
      (fieldScalarSecond L F a b) (fieldScalarThird L F a b c)

def fieldScalarThirdCap : List (ℝ × ℝ≥0) → ℝ → ℝ → ℝ → ℝ
  | [], _, _, D => D
  | av :: L, K, C, D => fieldThirdTransformCap av.1 K
      (fieldScalarSecondCap L K C) (fieldScalarThirdCap L K C D)

lemma fieldScalarThird_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {K C D : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C) (bc : ∀ z, |c z| ≤ D) :
    Measurable (fieldScalarThird L F a b c) ∧
      ∀ z, |fieldScalarThird L F a b c z| ≤ fieldScalarThirdCap L K C D := by
  induction L with
  | nil => exact ⟨hc, bc⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := ih ht
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    exact ⟨measurable_fieldThirdTransform av.1 av.2 hv.1 hm.1 hq.1 hr.1,
      fieldThirdTransform_bound av.1 av.2 hv.1 hv.2 hK hC hm.2 hq.2 hr.2⟩

lemma hasDerivAt_fieldScalarSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {K C D : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C) (bc : ∀ z, |c z| ≤ D)
    (dF : ∀ z, HasDerivAt F (a z) z)
    (da : ∀ z, HasDerivAt a (b z) z)
    (db : ∀ z, HasDerivAt b (c z) z) (z : ℝ) :
    HasDerivAt (fieldScalarSecond L F a b) (fieldScalarThird L F a b c z) z := by
  induction L generalizing z with
  | nil => exact db z
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := fieldScalarThird_regular L ht hF hG ha hb hc hK ba bb bc
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    have hd := hasDerivAt_fieldCurvatureTransform av.1 av.2 hv.1 hv.2
      hm.1 hq.1 hr.1 hK hC hm.2 hq.2 hr.2
      (hasDerivAt_fieldScalarValue L ht hF hG ha hK ba dF)
      (hasDerivAt_fieldScalarMean L ht hF hG ha hb hK ba bb dF da) (ih ht) z
    exact hd

lemma field_logCosh_third_derivative (z : ℝ) :
    HasDerivAt (fun y : ℝ => 1 / (Real.cosh y) ^ 2)
      (-2 * Real.tanh z / (Real.cosh z) ^ 2) z := by
  have hd := (hasDerivAt_const z (1 : ℝ)).div ((Real.hasDerivAt_cosh z).pow 2)
    (pow_ne_zero 2 (Real.cosh_pos z).ne')
  convert hd using 1
  simp only [Pi.pow_apply]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

lemma field_logCosh_third_bound (z : ℝ) :
    |-2 * Real.tanh z / (Real.cosh z) ^ 2| ≤ 2 := by
  have ht := field_abs_tanh_le_one z
  have hq := field_tanh_second_bound z
  have hh : |-2 * Real.tanh z / (Real.cosh z) ^ 2| =
      2 * |Real.tanh z| * |1 / (Real.cosh z) ^ 2| := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_div, abs_one]
    ring
  rw [hh]
  calc
    _ ≤ 2 * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hq
      (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

lemma hasDerivAt_fieldScalarLogCoshSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2))
      (fieldScalarThird L (fun z => Real.log (Real.cosh z)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2)
        (fun y => -2 * Real.tanh y / (Real.cosh y) ^ 2) z) z := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply hasDerivAt_fieldScalarSecond L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound
  · intro y
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
  · exact field_hasDerivAt_tanh
  · exact field_logCosh_third_derivative

end InvariantIsing

end

end OAI
