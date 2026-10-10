import OAI.NumberTheory.Ostmann.Construction.OriginalTupleLifts

namespace OAI

/-! # The original prime-product range supplies the strict Fourier grid margin -/

namespace Ostmann

theorem fourier_grid_margin_of_prime_scale (T R : ℝ) (L : ℕ)
    (hT : 1 ≤ T) (hL : (L : ℝ) ≤ Real.exp (T / 50))
    (hR : Real.exp (10 * T) ≤ R) :
    (L : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R := by
  have hpow : (L : ℝ) ^ 6 ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (T / 50) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 6
      _ = Real.exp (6 * (T / 50)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsmall : Real.exp (-200 * T) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
  have hfactor : (2 : ℝ) ≤ Real.exp (9 * T) := by linarith [Real.add_one_le_exp (9 * T)]
  calc
    _ ≤ 2 * Real.exp T := by linarith
    _ ≤ Real.exp (9 * T) * Real.exp T := mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    _ = Real.exp (10 * T) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ R := hR

end Ostmann

end OAI
