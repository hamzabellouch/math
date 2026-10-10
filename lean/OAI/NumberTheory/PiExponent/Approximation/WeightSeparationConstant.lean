import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace PiExponentApprox

theorem multiplicity_constant_le_coarse (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m) :
    2 * (k.factorial : ℝ) * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * (m.factorial : ℝ) * (1 + ((m : ℝ) + 2) / sigma) ^ m := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hfac : (k.factorial : ℝ) ≤ (m.factorial : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le hkm)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ m := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase) hkm
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hfac (by norm_num)) hpow
    (pow_nonneg hbase _) (by positivity)

theorem dimension_power_le_enlarged (m k : ℕ) (hkm : k ≤ m) :
    (k : ℝ) ^ k ≤ ((m : ℝ) + 2) ^ (m + 2) := by
  have hkle : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
  calc
    (k : ℝ) ^ k ≤ ((m : ℝ) + 2) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) k
    _ ≤ _ := pow_le_pow_right₀ (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
      (hkm.trans (Nat.le_add_right m 2))

theorem rectangular_multiplicity_constant_le_enlarged (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m) :
    (k : ℝ) ^ k * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hfactor : (k : ℝ) ^ k ≤ 2 * ((m : ℝ) + 2) ^ (m + 2) :=
    (dimension_power_le_enlarged m k hkm).trans (by
      have h : 0 ≤ ((m : ℝ) + 2) ^ (m + 2) := by positivity
      linarith)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase)
        (hkm.trans (Nat.le_add_right m 2))
  exact mul_le_mul hfactor hpow (pow_nonneg hbase _) (by positivity)

theorem multiplicity_constant_le_enlarged (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m) :
    2 * (k.factorial : ℝ) * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hfac : (k.factorial : ℝ) ≤ ((m : ℝ) + 2) ^ (m + 2) :=
    (by exact_mod_cast Nat.factorial_le_pow k : (k.factorial : ℝ) ≤ (k : ℝ) ^ k).trans
      (dimension_power_le_enlarged m k hkm)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase)
        (hkm.trans (Nat.le_add_right m 2))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfac (by norm_num)) hpow
    (pow_nonneg hbase _) (by positivity)

end PiExponentApprox

end OAI
