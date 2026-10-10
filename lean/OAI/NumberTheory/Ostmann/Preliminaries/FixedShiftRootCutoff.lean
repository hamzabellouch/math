import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace OAI

/-! # Integer-root cutoffs for fixed-shift sieving on arbitrary intervals -/

namespace Ostmann

open Filter

 theorem nthRoot_tendsto (k : ℕ) (hk : k ≠ 0) :
    Tendsto (Nat.nthRoot k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b ^ k)] with N hN
  exact (Nat.le_nthRoot_iff hk).mpr hN

 theorem nthRoot_log_comparison (k N : ℕ) (hk : k ≠ 0) (hN : 2 ≤ N)
    (hR : 2 ≤ Nat.nthRoot k N) :
    Real.log (N : ℝ) ≤ 2 * (k : ℝ) * Real.log (Nat.nthRoot k N : ℝ) := by
  let R := Nat.nthRoot k N
  have hRp : (0 : ℝ) < R := by dsimp [R]; exact_mod_cast (by omega : 0 < Nat.nthRoot k N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hupper : (N : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_pow_nthRoot_add_one hk N).le
  have hl := Real.log_le_log hNp hupper
  rw [Real.log_pow] at hl
  have hrbound : ((R + 1 : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
    push_cast
    have hh : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hrlog := Real.log_le_log (by positivity : (0 : ℝ) < (R + 1 : ℕ)) hrbound
  rw [Real.log_mul (by norm_num) hRp.ne'] at hrlog
  have h2log := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ R by exact_mod_cast hR)
  change Real.log (N : ℝ) ≤ 2 * (k : ℝ) * Real.log (R : ℝ)
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

 theorem fixedShiftRoot_square_cutoff (j N : ℕ) (hj : 1 ≤ j) :
    (Nat.nthRoot (20 * j) N ^ (10 * j)) ^ 2 ≤ N := by
  rw [← pow_mul]
  rw [show 10 * j * 2 = 20 * j by omega]
  exact Nat.pow_nthRoot_le (Or.inl (by omega : 20 * j ≠ 0))

end Ostmann

end OAI
