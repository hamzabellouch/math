import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands

namespace OAI

/-! The bounded-error form of partial summation needed for the padding
oscillation. The constants retain the uniform derivative bounds explicitly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem weighted_theta_error (c : ℕ → ℝ) (α K F D a b : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b))
    (hsize : ∀ x ∈ Set.Icc a b, |f x| ≤ F / x)
    (hdsize : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ D / x ^ 2)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ x in a..b, f x)| ≤
      (2 * F + D) * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hb1 : 1 < b := ha1.trans_le hab
  have hla : 1 ≤ Real.log a := by simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hxp (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hln (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log x ≠ 0 :=
    (zero_lt_one.trans_le (hlx x hx)).ne'
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |f x * (partialCoefficientSum c x - α * x)| ≤ F * K / Real.log a := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (F / x) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = F * K / Real.log x ^ 2 := by field_simp
      _ ≤ F * K / Real.log a := by
        apply div_le_div_of_nonneg_left (mul_nonneg hF hK) hlap
        have hm := Real.log_le_log ha0 hx.1
        nlinarith [sq_nonneg (Real.log x - 1), hlx x hx]
  have hderror (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |deriv f x * (partialCoefficientSum c x - α * x)| ≤
        (D * K) * (x⁻¹ / Real.log x ^ 2) := by
    have hx0 := hxp x hx
    have hl0 := hln x hx
    rw [abs_mul]
    calc
      _ ≤ (D / x ^ 2) * (K * x / Real.log x ^ 2) :=
        mul_le_mul (hdsize x hx) (hE x hx) (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxp x hx).ne').continuousWithinAt
  have hg : IntervalIntegrable (fun x : ℝ => (D * K) * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')).div
      (hclog.pow 2) (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (D * K)
  have hi : |∫ x in a..b, deriv f x * (partialCoefficientSum c x - α * x)| ≤
      D * K / Real.log a := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hderror x ⟨hx.1.le, hx.2⟩)) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hh
    apply hh.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (mul_nonneg hD hK) hbnonneg]
  rw [centered_partial_summation c α a b ha0.le hab f hf hdf]
  calc
    _ ≤ |f b * (partialCoefficientSum c b - α * b)| +
        |f a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ F * K / Real.log a + F * K / Real.log a + D * K / Real.log a :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩)) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI
