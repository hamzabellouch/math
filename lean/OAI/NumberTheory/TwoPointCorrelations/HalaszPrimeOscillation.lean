import OAI.NumberTheory.TwoPointCorrelations.HalaszPretentiousCenter
import OAI.NumberTheory.TwoPointCorrelations.OscillatoryThetaError

namespace OAI

/-! The moderate-frequency prime-phase step in MRT Lemma A.4.
The frequency dependence of partial summation is explicit, so a growing
frequency range can be paid for by the exponential prime-number error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_oscillatory_weight_bounds (t x : ℝ) (hx : 1 < x)
    (hl : 1 ≤ Real.log x) :
    |oscillatoryReciprocalLog t x| ≤ 2 / x ∧
      |deriv (oscillatoryReciprocalLog t) x| ≤ (|t| + 4) / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hg : |1 - Real.cos (t * Real.log x)| ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (t * Real.log x)]
  have hs : |t * Real.sin (t * Real.log x) / x| ≤ |t| / x := by
    rw [abs_div, abs_mul, abs_of_pos hx0]
    apply div_le_div_of_nonneg_right _ hx0.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one (t * Real.log x)) (abs_nonneg t)
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
      _ ≤ (|t| / x) * (1 / x) + 2 * (2 / x ^ 2) :=
        add_le_add (mul_le_mul hs hrec (abs_nonneg _) (by positivity))
          (mul_le_mul hg hdrec (abs_nonneg _) (by norm_num))
      _ = _ := by ring

theorem halasz_oscillatory_theta_error (c : ℕ → ℝ) (α K a b t : ℝ)
    (hK : 0 ≤ K) (ha : Real.exp 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * c n) -
      α * (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤
        (8 + |t|) * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hl (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (ha.trans hx.1)
  have hh := weighted_theta_error c α K 2 (|t| + 4) a b hK (by norm_num)
    (by positivity) ha hab (oscillatoryReciprocalLog t)
    (fun x hx => (oscillatoryReciprocalLog_hasDerivAt t x (hx1 x hx)).differentiableAt)
    (fun x hx => ?_)
    (fun x hx => (halasz_oscillatory_weight_bounds t x (hx1 x hx) (hl x hx)).1)
    (fun x hx => (halasz_oscillatory_weight_bounds t x (hx1 x hx) (hl x hx)).2) hE
  · convert hh using 1
    ring
  · have hxn : x ≠ 0 := (zero_lt_one.trans (hx1 x hx)).ne'
    have hln : Real.log x ≠ 0 := (Real.log_pos (hx1 x hx)).ne'
    have hc : ContDiffAt ℝ 2 (oscillatoryReciprocalLog t) x := by
      unfold oscillatoryReciprocalLog reciprocalLog
      fun_prop (disch := assumption)
    exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

lemma halasz_cosine_defect (x : ℝ) :
    (1 - Real.cos (2 * x)) / 4 ≤ 1 - |Real.cos x| := by
  have hc := Real.abs_cos_le_one x
  have hn := sq_nonneg (1 - |Real.cos x|)
  rw [Real.cos_two_mul]
  nlinarith [sq_abs (Real.cos x)]

lemma halasz_prime_cosine_defect (N : ℕ) (Y t : ℝ) :
    (∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
      (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ)) ≤
      4 * ∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
        (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  have h := halasz_cosine_defect (t * Real.log (p : ℝ) / 2)
  have he : 2 * (t * Real.log (p : ℝ) / 2) = t * Real.log (p : ℝ) := by ring
  rw [he] at h
  have h' : 1 - Real.cos (t * Real.log (p : ℝ)) ≤
      4 * (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) := by linarith
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h' (Nat.cast_nonneg p)

end TwoPointCorrelations

end OAI
