import OAI.NumberTheory.TwoPoint.Bounds.OscillatoryThetaError

namespace OAI

/-! The elementary logarithmic oscillatory integral behind the padding
prime estimate. All constants are absolute. -/

namespace TwoPointCorrelations

open MeasureTheory
open scoped Classical

lemma integral_inverse_square (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, (y ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((y ^ 2)⁻¹) y := by
    intro y hy
    have hy' : y ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hy
    have hy0 : y ≠ 0 := (ha.trans_le hy'.1).ne'
    convert! (hasDerivAt_inv hy0).neg using 1
    simp
  have hc : ContinuousOn (fun y : ℝ => (y ^ 2)⁻¹) (Set.Icc a b) := by
    intro y hy
    have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hy0)).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.intervalIntegrable_of_Icc hab)
  linarith

lemma cosine_log_tail (T a b : ℝ) (hT : 0 < T) (ha : 0 < a) (hab : a ≤ b)
    (hTa : 1 ≤ T * a) :
    |∫ y in a..b, Real.cos (T * y) / y| ≤ 3 := by
  have hb : 0 < b := ha.trans_le hab
  have hpos (y : ℝ) (hy : y ∈ Set.Icc a b) : 0 < y := ha.trans_le hy.1
  have hu (y : ℝ) : HasDerivAt (fun y => Real.sin (T * y) / T) (Real.cos (T * y)) y := by
    have hh := ((Real.hasDerivAt_sin (T * y)).comp y ((hasDerivAt_id y).const_mul T)).div_const T
    convert hh using 1
    · simp only [Function.comp_def, mul_comm T]
    · field_simp
  have hv (y : ℝ) (hy : y ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(y ^ 2)⁻¹) y := by
    apply hasDerivAt_inv
    have hy' : y ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hy
    exact (ha.trans_le hy'.1).ne'
  have hcos : IntervalIntegrable (fun y => Real.cos (T * y) / y) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (by fun_prop (disch := exact (hpos y hy).ne') :
      ContinuousAt (fun y => Real.cos (T * y) / y) y).continuousWithinAt
  have htail : IntervalIntegrable (fun y => Real.sin (T * y) / (T * y ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    have hy0 := (hpos y hy).ne'
    exact (by fun_prop (disch := positivity) :
      ContinuousAt (fun y => Real.sin (T * y) / (T * y ^ 2)) y).continuousWithinAt
  have hvin : IntervalIntegrable (fun y : ℝ => -(y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos y hy).ne')).neg).continuousWithinAt
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun y (_ : y ∈ Set.uIcc a b) => hu y) hv
    ((by fun_prop : Continuous (fun y => Real.cos (T * y))).intervalIntegrable a b) hvin
  have heq : (∫ y in a..b, Real.cos (T * y) / y) -
      (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)) =
      Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a) := by
    rw [← intervalIntegral.integral_sub hcos htail]
    convert hparts using 1
    · apply intervalIntegral.integral_congr
      intro y _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · field_simp
  have hendpoint (y : ℝ) (hy : a ≤ y) : |Real.sin (T * y) / (T * y)| ≤ 1 := by
    have hy0 : 0 < y := ha.trans_le hy
    rw [abs_div, abs_of_pos (mul_pos hT hy0)]
    apply (div_le_one (mul_pos hT hy0)).mpr
    exact (Real.abs_sin_le_one _).trans (hTa.trans (mul_le_mul_of_nonneg_left hy hT.le))
  have hg : IntervalIntegrable (fun y : ℝ => T⁻¹ * (y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro y hy
    exact (((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (hpos y hy).ne')).const_mul _).continuousWithinAt
  have hi : |∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)| ≤ 1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun y : ℝ => Real.sin (T * y) / (T * y ^ 2))
      (g := fun y : ℝ => T⁻¹ * (y ^ 2)⁻¹) hab
      (Filter.Eventually.of_forall (fun y hy => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hT (sq_pos_of_pos (hpos y ⟨hy.1.le, hy.2⟩)))]
        calc
          _ ≤ 1 / (T * y ^ 2) := div_le_div_of_nonneg_right (Real.abs_sin_le_one _)
            (mul_nonneg hT.le (sq_nonneg y))
          _ = _ := by simp [div_eq_mul_inv, mul_inv_rev, mul_comm])) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_inverse_square a b ha hab] at hh
    have hsmall : T⁻¹ * a⁻¹ ≤ 1 := by
      rw [← mul_inv_rev]
      exact (inv_le_one₀ (mul_pos ha hT)).mpr (by nlinarith)
    have hnonneg : 0 ≤ T⁻¹ * b⁻¹ := by positivity
    nlinarith
  have htriangle := abs_sub (Real.sin (T * b) / (T * b)) (Real.sin (T * a) / (T * a))
  have htriangle' := abs_add_le
    (Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a))
    (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2))
  have hformula : (∫ y in a..b, Real.cos (T * y) / y) =
      (Real.sin (T * b) / (T * b) - Real.sin (T * a) / (T * a)) +
      (∫ y in a..b, Real.sin (T * y) / (T * y ^ 2)) := by linarith
  rw [hformula]
  linarith [hendpoint a le_rfl, hendpoint b hab]

lemma logarithmic_oscillation_nonneg (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ ∫ y in a..b, (1 - Real.cos (t * y)) / y := by
  apply intervalIntegral.integral_nonneg hab
  intro y hy
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (ha.trans_le hy.1).le

lemma logarithmic_oscillation_lower_pos (T L : ℝ) (hT : 0 < T) (hT2 : T ≤ 2)
    (hL : 1 ≤ L) :
    Real.log (1 + L * T) - 5 ≤ ∫ y in (1 : ℝ)..L, (1 - Real.cos (T * y)) / y := by
  let A := max 1 T⁻¹
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hTA : 1 ≤ T * A := by
    calc
      1 = T * T⁻¹ := (mul_inv_cancel₀ hT.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le
  have hAT : A * T ≤ 2 := by
    by_cases hh : 1 ≤ T⁻¹
    · simp only [A, max_eq_right hh]
      rw [inv_mul_cancel₀ hT.ne']
      norm_num
    · simpa only [A, max_eq_left (le_of_not_ge hh), one_mul] using hT2
  by_cases hLA : L < A
  · have hsmall : L * T < 1 := by
      rcases lt_max_iff.mp hLA with hh | hh
      · exact False.elim (not_lt_of_ge hL hh)
      · have hm := mul_lt_mul_of_pos_right hh hT
        simpa only [inv_mul_cancel₀ hT.ne'] using hm
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + L * T)
    have hnonneg := logarithmic_oscillation_nonneg T 1 L (by norm_num) hL
    linarith
  have hAL : A ≤ L := le_of_not_gt hLA
  have hcont (a b : ℝ) (ha : 0 < a) :
      ContinuousOn (fun y => (1 - Real.cos (T * y)) / y) (Set.Icc a b) := by
    intro y hy
    have hy0 := (ha.trans_le hy.1).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y => (1 - Real.cos (T * y)) / y) y).continuousWithinAt
  have hhead : IntervalIntegrable (fun y => (1 - Real.cos (T * y)) / y) volume 1 A :=
    (hcont 1 A (by norm_num)).intervalIntegrable_of_Icc hA1
  have htail : IntervalIntegrable (fun y => (1 - Real.cos (T * y)) / y) volume A L :=
    (hcont A L hA).intervalIntegrable_of_Icc hAL
  have hrestrict : (∫ y in A..L, (1 - Real.cos (T * y)) / y) ≤
      ∫ y in (1 : ℝ)..L, (1 - Real.cos (T * y)) / y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hhead htail]
    have hh := logarithmic_oscillation_nonneg T 1 A (by norm_num) hA1
    linarith
  have hi : (∫ y in A..L, (1 - Real.cos (T * y)) / y) =
      Real.log (L / A) - ∫ y in A..L, Real.cos (T * y) / y := by
    have hi₁ : IntervalIntegrable (fun y : ℝ => 1 / y) volume A L := by
      apply ContinuousOn.intervalIntegrable_of_Icc (h := hAL)
      intro y hy
      exact (continuousAt_const.div continuousAt_id (hA.trans_le hy.1).ne').continuousWithinAt
    have hi₂ : IntervalIntegrable (fun y : ℝ => Real.cos (T * y) / y) volume A L := by
      apply ContinuousOn.intervalIntegrable_of_Icc (h := hAL)
      intro y hy
      have hy0 := (hA.trans_le hy.1).ne'
      exact (by fun_prop (disch := assumption) :
        ContinuousAt (fun y => Real.cos (T * y) / y) y).continuousWithinAt
    rw [← integral_one_div_of_pos hA hLp, ← intervalIntegral.integral_sub hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hcos := (abs_le.mp (cosine_log_tail T A L hT hA hAL hTA)).2
  have hratio : 1 ≤ L / A := (le_div_iff₀ hA).mpr (by simpa using hAL)
  have hsize : 1 + L * T ≤ 3 * (L / A) := by
    have hh := mul_le_mul_of_nonneg_right hAT (div_nonneg hLp.le hA.le)
    have he : (A * T) * (L / A) = L * T := by field_simp
    rw [he] at hh
    linarith
  have hlog : Real.log (1 + L * T) ≤ Real.log (L / A) + 2 := by
    have hh := Real.log_le_log (by positivity : 0 < 1 + L * T) hsize
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (div_pos hLp hA).ne'] at hh
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  rw [hi] at hrestrict
  linarith

theorem logarithmic_oscillation_lower (t L : ℝ) (ht : |t| ≤ 2) (hL : 1 ≤ L) :
    Real.log (1 + L * |t|) - 5 ≤ ∫ y in (1 : ℝ)..L, (1 - Real.cos (t * y)) / y := by
  by_cases ht0 : t = 0
  · subst t
    simp
  have hh := logarithmic_oscillation_lower_pos |t| L (abs_pos.mpr ht0) ht hL
  have hcos (y : ℝ) : Real.cos (|t| * y) = Real.cos (t * y) := by
    rcases le_or_gt 0 t with ht' | ht'
    · rw [abs_of_nonneg ht']
    · rw [abs_of_neg ht', neg_mul, Real.cos_neg]
  simpa only [hcos] using hh

end TwoPointCorrelations

end OAI
