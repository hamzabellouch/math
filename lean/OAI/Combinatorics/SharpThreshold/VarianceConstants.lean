import Mathlib

namespace OAI

noncomputable section

namespace Problem313

/-- A coarse bound sufficient for absorbing the low Fourier levels. -/
theorem variance_decay_constant {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hlog : t / 3 ≤ Real.log m) :
    4 * m ^ (-(1 : ℝ) / 4) ≤ 1152 / t ^ 2 := by
  have hexp : t ^ 2 / 288 ≤ Real.exp (t / 12) := by
    have h := Real.pow_div_factorial_le_exp (t / 12) (show 0 ≤ t / 12 by positivity) 2
    norm_num at h
    nlinarith
  have hcancel : Real.exp (t / 12) * Real.exp (-(t / 12)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hdecay : t ^ 2 * Real.exp (-(t / 12)) ≤ 288 := by
    have h := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-(t / 12)))
    rw [hcancel] at h
    nlinarith
  have hpow : m ^ (-(1 : ℝ) / 4) ≤ Real.exp (-(t / 12)) := by
    rw [Real.rpow_def_of_pos hm]
    apply Real.exp_le_exp.mpr
    linarith
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  have h := mul_le_mul_of_nonneg_left hpow (sq_nonneg t)
  nlinarith

/-- Cancellation of the bias and comparison of logarithms in the Fourier tail. -/
theorem variance_tail_constant {t m σ : ℝ} (ht : 0 < t)
    (hlog : t / 3 ≤ Real.log m) (hσ : 0 < σ) :
    2 * σ ^ 2 / (σ * Real.log m / 64) ^ 2 ≤ 73728 / t ^ 2 := by
  have hl : 0 < Real.log m := by linarith
  have heq : 2 * σ ^ 2 / (σ * Real.log m / 64) ^ 2 =
      8192 / (Real.log m) ^ 2 := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hl) (sq_pos_of_pos ht)).mpr
  have htl : t ≤ 3 * Real.log m := by linarith
  have hs := mul_le_mul htl htl ht.le (by positivity : 0 ≤ 3 * Real.log m)
  nlinarith

/-- A numerical bound for the sum of low-degree and spectral-tail contributions.
Only the lower bound on `log m` is needed; no floor or exponential monotonicity
arguments enter this estimate. -/
theorem variance_constant_bound {t m σ : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hlog : t / 3 ≤ Real.log m) (hσ : 0 < σ) :
    4 * m ^ (-(1 : ℝ) / 4) + 2 * σ ^ 2 / (σ * Real.log m / 64) ^ 2 ≤
      (2 : ℝ) ^ 17 / t ^ 2 := by
  have h₁ := variance_decay_constant ht hm hlog
  have h₂ := variance_tail_constant ht hlog hσ
  have h₃ : (1152 : ℝ) / t ^ 2 + 73728 / t ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    norm_num
  linarith

end Problem313

end

end OAI
