import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBilinearComparison

namespace OAI

/-! # The explicit dyadic-bin count costs only an arbitrarily small power -/

namespace Ostmann

 theorem quadratic_dyadic_count_bound (ε : ℝ) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      (1 + (ε * Real.log 2)⁻¹) * (N : ℝ) ^ ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast hN) hε.le
  have hb := Real.natLog_le_logb N 2
  change (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 at hb
  calc
    _ = (Nat.log 2 N : ℝ) + 1 := by push_cast; rfl
    _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ ((N : ℝ) ^ ε / ε) / Real.log 2 + (N : ℝ) ^ ε :=
      add_le_add (div_le_div_of_nonneg_right (Real.log_natCast_le_rpow_div N hε) hl.le) hp
    _ = _ := by field_simp; ring

 theorem quadratic_dyadic_pair_count_bound (ε : ℝ) (hε : 0 < ε)
    (N₁ N₂ : ℕ) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) :
    ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) ≤
      (1 + (ε * Real.log 2)⁻¹) ^ 2 * ((N₁ : ℝ) * N₂) ^ ε := by
  have hh := mul_le_mul (quadratic_dyadic_count_bound ε hε N₁ hN₁)
    (quadratic_dyadic_count_bound ε hε N₂ hN₂) (by positivity)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
  simp only [Nat.cast_add, Nat.cast_one] at hh ⊢
  apply hh.trans_eq
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

end Ostmann

end OAI
