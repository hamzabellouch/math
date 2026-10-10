import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticSumRate

namespace OAI

/-! # The actual degree and frequency scales in the arithmetic comparison -/

namespace Ostmann
open Filter

theorem moving_arithmetic_degree_bound (n r₀ k : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ((2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4) : ℕ) : ℝ) ≤
      ((2 ^ n : ℕ) : ℝ) * ((r₀ : ℝ) + (k : ℝ) ^ 4 + 4 * n + 4) * L := by
  have hm := spectatorBulkCount_upper k L (by linarith)
  have hc : 0 ≤ (r₀ : ℝ) + 4 * n + 4 := by positivity
  have hh := mul_le_mul_of_nonneg_left hL hc
  have hsum : (r₀ : ℝ) + spectatorBulkCount k L + 4 * n + 4 ≤
      ((r₀ : ℝ) + (k : ℝ) ^ 4 + 4 * n + 4) * L := by nlinarith
  calc
    _ = ((2 ^ n : ℕ) : ℝ) * ((r₀ : ℝ) + spectatorBulkCount k L + 4 * n + 4) := by
      push_cast
      rfl
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
        (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)

theorem moving_arithmetic_frequency_bound (k : ℕ) (A L : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L) :
    Real.log (Real.exp (A * spectatorBulkCount k L)) ≤ (A * (k : ℝ) ^ 4) * L := by
  rw [Real.log_exp]
  exact (mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL) hA).trans_eq
    (mul_assoc _ _ _).symm

end Ostmann

end OAI
