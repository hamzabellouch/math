import OAI.NumberTheory.Ostmann.Characters.SparseTensorPolynomial

namespace OAI

/-! # A concrete linear truncation cutoff for the sparse weight -/

namespace Ostmann

theorem sparse_grid_ratio_le_exp : (100 / 103 : ℝ) ≤ Real.exp (-1 / 40) := by
  have hh := Real.add_one_le_exp (-1 / 40 : ℝ)
  linarith

theorem sparse_truncation_constant_le_exp :
    (2 / (1 - 100 / 103) ^ 2 : ℝ) ≤ Real.exp 14 := by
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11 / 4)
    (show (11 / 4 : ℝ) ≤ Real.exp (7 / 4) by linarith [Real.add_one_le_exp (7 / 4 : ℝ)]) 8
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh ⊢
  linarith

/-- The fixed choice `K >= 1000 L` controls both the scalar and operator tails.
Only the harmonic-mass bound `H <= L` remains to be supplied by the prime band. -/
theorem sparse_truncation_error_rate (L H : ℝ) (K : ℕ)
    (hL : 1 ≤ L) (hH : H ≤ L) (hK : 1000 * L ≤ K) :
    2 * Real.exp (6 * H) * (100 / 103 : ℝ) ^ (K + 1) / (1 - 100 / 103) ^ 2 ≤
      Real.exp (-5 * L) := by
  have hq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100 / 103) sparse_grid_ratio_le_exp (K + 1)
  rw [← Real.exp_nat_mul] at hq
  have hc := sparse_truncation_constant_le_exp
  calc
    _ = (2 / (1 - 100 / 103) ^ 2 : ℝ) * Real.exp (6 * H) * (100 / 103 : ℝ) ^ (K + 1) := by ring
    _ ≤ Real.exp 14 * Real.exp (6 * H) * Real.exp ((K + 1 : ℕ) * (-1 / 40 : ℝ)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hq (by positivity) (by positivity)
    _ = Real.exp (14 + 6 * H + (K + 1 : ℕ) * (-1 / 40 : ℝ)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-5 * L) := Real.exp_le_exp.mpr (by push_cast; linarith)

end Ostmann

end OAI
