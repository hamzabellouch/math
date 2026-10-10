import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.DescentDecay

/-- Linear losses are negligible compared to the quarter-power exponential. -/
theorem tendsto_linear_mul_exp_neg_quarter (A B : ℝ) :
    Tendsto (fun S : ℝ => (A * S + B) * Real.exp (-(S ^ (1 / 4 : ℝ))))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun S : ℝ => S ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h4 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp ht
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp ht
  have h := (h4.const_mul A).add (h0.const_mul B)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with S hS
  dsimp
  have hp : (S ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = S := by
    rw [← Real.rpow_mul_natCast hS]
    norm_num
  rw [hp]
  ring

/-- A useful pointwise eventual version, with an absolute rather than relative error. -/
theorem eventually_linear_le_exp_quarter (A B : ℝ) :
    ∀ᶠ S : ℝ in atTop, A * S + B ≤ Real.exp (S ^ (1 / 4 : ℝ)) := by
  have h := (tendsto_linear_mul_exp_neg_quarter A B).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h] with S hS
  rw [Real.exp_neg, ← div_eq_mul_inv] at hS
  have hh := (div_lt_iff₀ (Real.exp_pos (S ^ (1 / 4 : ℝ)))).mp hS
  simpa using hh.le

/-- The polynomial loss from a localized Fourier packet fits the original descent budget. -/
theorem eventually_polynomial_loss_absorbed (A B r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 1 ≤ r) :
    ∀ᶠ S : ℝ in atTop,
      1 + (A * S + B) * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
        Real.exp (2 * S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_linear_le_exp_quarter A (B + 1),
    eventually_ge_atTop (0 : ℝ)] with S hlinear hS
  have ht : 0 ≤ S ^ (1 / 4 : ℝ) := Real.rpow_nonneg hS _
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have htr : 0 ≤ S ^ (1 / 4 : ℝ) / r := div_nonneg ht hr0.le
  have he1 : 1 ≤ Real.exp (S ^ (1 / 4 : ℝ) / r) := Real.one_le_exp_iff.mpr htr
  have he2 : Real.exp (S ^ (1 / 4 : ℝ) / r) ≤ Real.exp (S ^ (1 / 4 : ℝ)) :=
    Real.exp_le_exp.mpr (div_le_self ht hr)
  calc
    1 + (A * S + B) * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
        (A * S + B + 1) * Real.exp (S ^ (1 / 4 : ℝ) / r) := by nlinarith
    _ ≤ (A * S + B + 1) * Real.exp (S ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left he2
        (add_nonneg (add_nonneg (mul_nonneg hA hS) hB) zero_le_one)
    _ ≤ Real.exp (S ^ (1 / 4 : ℝ)) * Real.exp (S ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      simpa only [add_assoc] using hlinear
    _ = Real.exp (2 * S ^ (1 / 4 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

/-- Variable polynomial coefficients can be dominated uniformly before absorption. -/
theorem eventually_polynomial_loss_absorbed_of_le (A B r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 1 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ P : ℝ, P ≤ A * S + B →
      1 + P * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
        Real.exp (2 * S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_polynomial_loss_absorbed A B r hA hB hr] with S hS
  intro P hP
  have hh := mul_le_mul_of_nonneg_right hP (Real.exp_pos (S ^ (1 / 4 : ℝ) / r)).le
  linarith

end Problem337.DescentDecay

end

end OAI
