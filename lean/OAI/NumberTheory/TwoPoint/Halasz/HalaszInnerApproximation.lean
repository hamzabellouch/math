import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeConvolution

namespace OAI

/-! A complex-valued approximation, not just a norm bound, permits a second
application of the prime convolution inside the first one. -/

namespace TwoPointCorrelations

open Finset

lemma halasz_prime_log_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) :
    ‖(∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
      halaszPrimeConvolution f M‖ ≤ (halaszPrimePowerConstant + 1) * (M : ℝ) := by
  have he := halasz_logarithmic_sum_error f hf M hM
  have hp := halasz_log_sum_prime_error f hf hmul M
  have ht := norm_add_le
    ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 M, f n * (Real.log (n : ℝ) : ℂ))
    ((∑ n ∈ Icc 1 M, f n * (Real.log (n : ℝ) : ℂ)) -
      halaszPrimeConvolution f M)
  rw [sub_add_sub_cancel] at ht
  linarith

lemma halasz_prime_inner_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 2 ≤ M) :
    ‖(∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log (M : ℝ) : ℂ)‖ ≤
      (halaszPrimePowerConstant + 1) * (M : ℝ) / Real.log (M : ℝ) := by
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hc : (Real.log (M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlog
  have he : (∑ n ∈ Icc 1 M, f n) -
      halaszPrimeConvolution f M / (Real.log (M : ℝ) : ℂ) =
      ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
        halaszPrimeConvolution f M) / (Real.log (M : ℝ) : ℂ) := by
    field_simp
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (halasz_prime_log_approximation f hf hmul M (by omega))
    (le_of_lt hlog)

noncomputable def halaszInnerErrorConstant : ℝ :=
  halaszPrimePowerConstant + 1 + Real.log 2

lemma halaszInnerErrorConstant_nonneg : 0 ≤ halaszInnerErrorConstant := by
  unfold halaszInnerErrorConstant
  have hC := halaszPrimePowerConstant_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- The logarithm may use the real cutoff, while the sum and convolution
retain the exact natural cutoff. Their rounding error is uniformly O(x). -/
lemma halasz_real_log_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) {x : ℝ} (hMx : (M : ℝ) ≤ x) (hxM : x ≤ 2 * M) :
    ‖(∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
      halaszPrimeConvolution f M‖ ≤ halaszInnerErrorConstant * x := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hx0 : 0 < x := hM0.trans_le hMx
  have hlog0 : 0 ≤ Real.log x - Real.log (M : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hM0 hMx)
  have hlog2 : Real.log x - Real.log (M : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_log hx0 hxM
    rw [Real.log_mul (by norm_num) hM0.ne'] at h
    linarith
  have he : (∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
      halaszPrimeConvolution f M =
      (∑ n ∈ Icc 1 M, f n) * ((Real.log x - Real.log (M : ℝ) : ℝ) : ℂ) +
      ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
        halaszPrimeConvolution f M) := by push_cast; ring
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ Icc 1 M, f n) * ((Real.log x - Real.log (M : ℝ) : ℝ) : ℂ)‖ +
        ‖(∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
          halaszPrimeConvolution f M‖ := norm_add_le _ _
    _ ≤ (M : ℝ) * Real.log 2 + (halaszPrimePowerConstant + 1) * M := by
      apply add_le_add _ (halasz_prime_log_approximation f hf hmul M hM)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
      exact mul_le_mul (halasz_bounded_prefix_norm f hf M) hlog2 hlog0 (Nat.cast_nonneg _)
    _ = halaszInnerErrorConstant * (M : ℝ) := by unfold halaszInnerErrorConstant; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMx halaszInnerErrorConstant_nonneg

lemma halasz_real_inner_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) {x : ℝ} (hx : 1 < x)
    (hMx : (M : ℝ) ≤ x) (hxM : x ≤ 2 * M) :
    ‖(∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log x : ℂ)‖ ≤
      halaszInnerErrorConstant * x / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hc : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlog
  have he : (∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log x : ℂ) =
      ((∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
        halaszPrimeConvolution f M) / (Real.log x : ℂ) := by field_simp
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (halasz_real_log_approximation f hf hmul M hM hMx hxM)
    hlog.le

end TwoPointCorrelations

end OAI
