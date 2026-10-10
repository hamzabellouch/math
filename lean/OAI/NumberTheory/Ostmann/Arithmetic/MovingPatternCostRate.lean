import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # The actual equality-pattern cost fits the source's error budget -/

namespace Ostmann
open Filter

/-- All equality patterns and representative-prior losses contribute only a
fixed-depth exponential in L when p times its prior is at most exp(C L). -/
theorem movingPattern_total_cost_le_exp (n : ℕ) (C L : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L) :
    (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (C * L))) ^ (4 * n * 2 ^ n) ≤
      Real.exp ((((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * C * L) := by
  let J := 4 * n * 2 ^ n
  have hCL : 1 ≤ C * L := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ C * L := mul_le_mul hC hL (by norm_num) (by linarith)
  have he : (2 : ℝ) ≤ Real.exp (C * L) := by
    have h := Real.add_one_le_exp (C * L)
    linarith
  rw [max_eq_right he]
  calc
    _ ≤ (Real.exp (C * L)) ^ (J ^ 2) * (Real.exp (C * L)) ^ J :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) he _) (by positivity)
    _ = Real.exp (((J ^ 2 + J : ℕ) : ℝ) * C * L) := by
      rw [← pow_add, ← Real.exp_nat_mul]
      congr 1
      ring

/-- The proved pattern count can be inserted into the actual internal-prime
saving, together with the large pointwise spectator factor from (8.21). -/
theorem movingPattern_internal_error_rate (n : ℕ) (C B c : ℝ)
    (hC : 1 ≤ C) (_hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (C * L))) ^ (4 * n * 2 ^ n)) *
        Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        Real.exp (-c * Real.exp ((1 / 100 : ℝ) * L)) ≤
      Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  let K : ℝ := ((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ)
  let D := B + K * C
  filter_upwards [internal_prime_error D c hc, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  have hK : 0 ≤ K := by positivity
  have hC0 : 0 ≤ C := by linarith
  have hpow : L ≤ L ^ 2 := by nlinarith
  have hKL : K * C * L ≤ K * C * L ^ 2 :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg hK hC0)
  have hrest : B * L * Real.exp ((1 / 1000 : ℝ) * L) ≤
      D * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    dsimp only [D]
    linarith [mul_nonneg hK hC0]
  have hexp : K * C * L + (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) ≤
      D * L ^ 2 + D * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    dsimp only [D] at *
    nlinarith
  apply le_trans _ hrate
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  calc
    _ ≤ Real.exp (K * C * L) * Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) :=
      mul_le_mul_of_nonneg_right (movingPattern_total_cost_le_exp n C L hC hL) (Real.exp_nonneg _)
    _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hexp

end Ostmann

end OAI
