import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

noncomputable section

namespace MatrixMultiplication.RectangularRateLimit

open Filter
open scoped Topology

theorem eventually_two_le_of_positive_log_rate
    {a : ℕ → ℕ} {scale : ℕ → ℝ} {A : ℝ}
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (positive : 0 < A) : ∀ᶠ n in atTop, 2 ≤ a n := by
  filter_upwards [rate.eventually_const_lt positive, scale_positive] with n hn hs
  have hlog : 0 < Real.log (a n : ℝ) := (div_pos_iff_of_pos_right hs).mp hn
  have ha : (1 : ℝ) < a n := (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlog
  have : 1 < a n := by exact_mod_cast ha
  omega

theorem eventually_aspect_of_rate_gap
    {a b : ℕ → ℕ} {scale : ℕ → ℝ} {A B k : ℝ}
    (a_positive : ∀ n, 0 < a n) (b_positive : ∀ n, 0 < b n)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (a_rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (b_rate : Tendsto (fun n => Real.log (b n : ℝ) / scale n) atTop (𝓝 B))
    (gap : k * A < B) : ∀ᶠ n in atTop, (a n : ℝ) ^ k ≤ (b n : ℝ) := by
  filter_upwards [(a_rate.const_mul k).eventually_lt b_rate gap, scale_positive]
    with n hn hs
  have hlog : k * Real.log (a n : ℝ) < Real.log (b n : ℝ) := by
    apply (div_lt_div_iff_of_pos_right hs).mp
    simpa only [mul_div_assoc] using hn
  have ha : (0 : ℝ) < a n := Nat.cast_pos.mpr (a_positive n)
  have hb : (0 : ℝ) < b n := Nat.cast_pos.mpr (b_positive n)
  apply le_of_lt
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos ha k) hb).mp
  simpa only [Real.log_rpow ha] using hlog

theorem rate_inequality_of_log_bounds
    {a multiplicity rank : ℕ → ℕ} {scale : ℕ → ℝ} {A M R exponent : ℝ}
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (a_rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (multiplicity_rate : Tendsto
      (fun n => Real.log (multiplicity n : ℝ) / scale n) atTop (𝓝 M))
    (rank_rate : Tendsto (fun n => Real.log (rank n : ℝ) / scale n) atTop (𝓝 R))
    (finite_bound : ∀ᶠ n in atTop,
      exponent * Real.log (a n : ℝ) ≤
        Real.log (rank n : ℝ) - Real.log (multiplicity n : ℝ)) :
    exponent * A ≤ R - M := by
  apply le_of_tendsto_of_tendsto (a_rate.const_mul exponent)
    (rank_rate.sub multiplicity_rate)
  filter_upwards [finite_bound, scale_positive] with n hn hs
  have h := div_le_div_of_nonneg_right hn hs.le
  simpa only [mul_div_assoc, sub_div] using h

theorem exponent_le_of_finite_asi
    {a b multiplicity rank : ℕ → ℕ} {scale : ℕ → ℝ}
    {A B M R k exponent : ℝ}
    (a_positive : ∀ n, 0 < a n) (b_positive : ∀ n, 0 < b n)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (a_rate : Tendsto (fun n => Real.log (a n : ℝ) / scale n) atTop (𝓝 A))
    (b_rate : Tendsto (fun n => Real.log (b n : ℝ) / scale n) atTop (𝓝 B))
    (multiplicity_rate : Tendsto
      (fun n => Real.log (multiplicity n : ℝ) / scale n) atTop (𝓝 M))
    (rank_rate : Tendsto (fun n => Real.log (rank n : ℝ) / scale n) atTop (𝓝 R))
    (positive : 0 < A) (gap : k * A < B)
    (finite_asi : ∀ n, 2 ≤ a n → (a n : ℝ) ^ k ≤ (b n : ℝ) →
      exponent * Real.log (a n : ℝ) ≤
        Real.log (rank n : ℝ) - Real.log (multiplicity n : ℝ)) :
    exponent ≤ (R - M) / A := by
  apply (le_div_iff₀ positive).mpr
  apply rate_inequality_of_log_bounds scale_positive a_rate multiplicity_rate rank_rate
  filter_upwards [eventually_two_le_of_positive_log_rate scale_positive a_rate positive,
    eventually_aspect_of_rate_gap a_positive b_positive scale_positive a_rate b_rate gap]
    with n ha hab
  exact finite_asi n ha hab

end MatrixMultiplication.RectangularRateLimit

end

end OAI
