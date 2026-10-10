import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # Absorbing the number of giant residue pairs -/

namespace Ostmann
open Filter

theorem giant_residue_sum_error_rate (K : ℝ) (hK : 0 < K) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℕ, 0 < q →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      (q : ℝ) ^ 2 * K * Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  let C := |Real.log K| + 2
  filter_upwards [arithmetic_error_absorption (12 / 1000) (125 / 10000) (1225 / 100000)
    C 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hL hL1
  intro q hq hlog
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hfactor : (q : ℝ) ^ 2 * K ≤
      Real.exp (C * L ^ 0 + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    rw [← Real.exp_log (mul_pos (pow_pos hq0 2) hK), Real.exp_le_exp,
      Real.log_mul (pow_ne_zero 2 hq0.ne') hK.ne', Real.log_pow]
    have hC : 2 ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log K)]
    have hClog : Real.log K ≤ C := by dsimp [C]; linarith [le_abs_self (Real.log K)]
    have hLC : 2 ≤ C * L := le_trans hC (le_mul_of_one_le_right (by positivity : 0 ≤ C) hL1)
    have he := mul_le_mul_of_nonneg_right hLC (Real.exp_pos ((12 / 1000 : ℝ) * L)).le
    simp only [pow_zero, mul_one]
    linarith
  exact (mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le).trans
    (by simpa only [one_mul, neg_mul] using hL)

end Ostmann

end OAI
