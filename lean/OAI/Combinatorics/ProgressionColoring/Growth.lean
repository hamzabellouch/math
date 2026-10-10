import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- The integer logarithm in the product construction is the floor of the
real base-two logarithm. -/
theorem natLog_two_eq_floor_log (r : ℕ) :
    Nat.log 2 r = ⌊Real.log (r : ℝ) / Real.log 2⌋₊ := by
  simpa [Real.logb] using (Real.natFloor_logb_natCast 2 r).symm

/-- A uniform lower estimate for the number of usable binary digits. -/
theorem log_div_two_log_two_le_natLog {r : ℕ} (hr : 2 ≤ r) :
    Real.log (r : ℝ) / (2 * Real.log 2) ≤ (Nat.log 2 r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hm : 1 ≤ Nat.log 2 r := Nat.log_pos (by omega) hr
  have hmreal : (1 : ℝ) ≤ (Nat.log 2 r : ℝ) := by exact_mod_cast hm
  have hp : (r : ℝ) < (2 : ℝ) ^ (Nat.log 2 r + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < 2) r)
  have hupper := Real.log_lt_log hrpos hp
  rw [Real.log_pow] at hupper
  simp only [Nat.cast_add, Nat.cast_one] at hupper
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).2
  nlinarith

/-- A bound of the form `k^(a*k)` with positive fixed `a` forces the full
kth-root limit, with no subsequence restriction. -/
theorem tendsto_kthRoot_of_eventually_rpow_bound
    {F : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (h : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (a * k) ≤ F k) :
    Tendsto (fun k : ℕ => (F k) ^ (1 / (k : ℝ))) atTop atTop := by
  have hbase : Tendsto (fun k : ℕ => (k : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with k hk hkpos
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  calc
    (k : ℝ) ^ a = ((k : ℝ) ^ (a * k)) ^ (1 / (k : ℝ)) := by
      rw [← Real.rpow_mul hkreal.le]
      congr 1
      field_simp
    _ ≤ (F k) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hkreal.le _) hk (by positivity)

end QuantitativeVanDerWaerden

end OAI
