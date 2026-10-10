import OAI.NumberTheory.TwoPointCorrelations.WeightedThetaError
import OAI.NumberTheory.TwoPointCorrelations.PaddingCharacteristic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Uniform partial summation for `(1-cos(t log p))/p`, with `|t|≤2`.
The oscillatory prime estimate is deduced from the theta error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def oscillatoryReciprocalLog (t x : ℝ) : ℝ :=
  (1 - Real.cos (t * Real.log x)) * reciprocalLog x

lemma reciprocalLog_size {x : ℝ} (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |reciprocalLog x| ≤ 1 / x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  unfold reciprocalLog
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hl0).mpr
  have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hx0.le)
  simpa only [mul_one, one_div] using hh

lemma reciprocalLog_deriv_size {x : ℝ} (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |deriv reciprocalLog x| ≤ 2 / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ (2 * Real.log x ^ 2) / (x ^ 2 * Real.log x ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (Real.log x - 1)]
    _ = _ := by field_simp

lemma oscillatoryReciprocalLog_hasDerivAt (t x : ℝ) (hx : 1 < x) :
    HasDerivAt (oscillatoryReciprocalLog t)
      ((t * Real.sin (t * Real.log x) / x) * reciprocalLog x +
        (1 - Real.cos (t * Real.log x)) * deriv reciprocalLog x) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hg := ((Real.hasDerivAt_cos (t * Real.log x)).comp x
    ((Real.hasDerivAt_log hx0).const_mul t)).const_sub 1
  have hh := hg.mul (reciprocalLog_hasDerivAt hx)
  convert hh using 1
  · rfl
  · rw [(reciprocalLog_hasDerivAt hx).deriv]
    simp only [div_eq_mul_inv, Function.comp_def]
    ring

lemma oscillatoryReciprocalLog_bounds (t x : ℝ) (ht : |t| ≤ 2)
    (hx : 1 < x) (hl : 1 ≤ Real.log x) :
    |oscillatoryReciprocalLog t x| ≤ 2 / x ∧
      |deriv (oscillatoryReciprocalLog t) x| ≤ 6 / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hg : |1 - Real.cos (t * Real.log x)| ≤ 2 :=
    (abs_of_nonneg (one_sub_cos_bounds _).1).trans_le (one_sub_cos_bounds _).2
  have hs : |t * Real.sin (t * Real.log x) / x| ≤ 2 / x := by
    rw [abs_div, abs_mul, abs_of_pos hx0]
    apply div_le_div_of_nonneg_right _ hx0.le
    exact (mul_le_mul ht (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (mul_one 2)
  have hrec := reciprocalLog_size hx hl
  have hdrec := reciprocalLog_deriv_size hx hl
  constructor
  · unfold oscillatoryReciprocalLog
    rw [abs_mul]
    calc
      _ ≤ 2 * (1 / x) := mul_le_mul hg hrec (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  · rw [(oscillatoryReciprocalLog_hasDerivAt t x hx).deriv]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (2 / x) * (1 / x) + 2 * (2 / x ^ 2) :=
        add_le_add (mul_le_mul hs hrec (abs_nonneg _) (by positivity))
          (mul_le_mul hg hdrec (abs_nonneg _) (by norm_num))
      _ = _ := by field_simp; ring

theorem oscillatory_theta_error (c : ℕ → ℝ) (α K a b t : ℝ)
    (hK : 0 ≤ K) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (ht : |t| ≤ 2)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * c n) -
      α * (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤ 10 * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hl (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (ha.trans hx.1)
  suffices hh : |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * c n) -
      α * (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤ (2 * 2 + 6) * K / Real.log a by
    norm_num at hh
    exact hh
  apply weighted_theta_error c α K 2 6 a b hK (by norm_num) (by norm_num) ha hab
  · intro x hx
    exact (oscillatoryReciprocalLog_hasDerivAt t x (hx1 x hx)).differentiableAt
  · intro x hx
    have hxn : x ≠ 0 := (zero_lt_one.trans (hx1 x hx)).ne'
    have hln : Real.log x ≠ 0 := (Real.log_pos (hx1 x hx)).ne'
    have hc : ContDiffAt ℝ 2 (oscillatoryReciprocalLog t) x := by
      unfold oscillatoryReciprocalLog reciprocalLog
      fun_prop (disch := assumption)
    exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  · exact fun x hx => (oscillatoryReciprocalLog_bounds t x ht (hx1 x hx) (hl x hx)).1
  · exact fun x hx => (oscillatoryReciprocalLog_bounds t x ht (hx1 x hx) (hl x hx)).2
  · exact hE

end TwoPointCorrelations

end OAI
