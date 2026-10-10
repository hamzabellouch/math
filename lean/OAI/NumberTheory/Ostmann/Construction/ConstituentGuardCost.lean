import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalComplexity

namespace OAI

/-! # Polynomial counts control the original prime-guard loss -/
namespace Ostmann

theorem constituent_guard_cost_le_exp (n J U B : ℕ) (s S a b m : ℝ)
    (hs : 0 ≤ s) (hsS : s ≤ S) (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hJ : (J : ℝ) ≤ a * (1 + m)) (hU : (U : ℝ) ≤ a * (1 + m) ^ 2)
    (hB : (B : ℝ) ≤ b * (1 + m)) :
    s ^ (2 ^ n) * s ^ (2 ^ n) * ((J : ℝ) * (B : ℝ) ^ (n + 1) + U) ≤
      Real.exp ((2 * (2 ^ n : ℕ) * S + a * (b ^ (n + 1) + 1)) * (1 + m) ^ (n + 2)) := by
  let t := 1 + m
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := by linarith
  have hS : 0 ≤ S := hs.trans hsS
  have htp : 1 ≤ t ^ (n + 2) := one_le_pow₀ ht
  have hpow : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * t ^ (n + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg B) hB _
  have hpoly : (J : ℝ) * (B : ℝ) ^ (n + 1) + U ≤
      a * (b ^ (n + 1) + 1) * t ^ (n + 2) := by
    have hmul := mul_le_mul hJ hpow (by positivity) (by positivity : 0 ≤ a * t)
    have hU' := hU.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ht (show 2 ≤ n + 2 by omega)) ha)
    have hid : a * t * (b ^ (n + 1) * t ^ (n + 1)) =
        a * b ^ (n + 1) * t ^ (n + 2) := by rw [pow_succ t (n + 1)]; ring
    rw [hid] at hmul
    linarith
  have hse : s ≤ Real.exp S := hsS.trans (by linarith [Real.add_one_le_exp S])
  have hsp := pow_le_pow_left₀ hs hse (2 ^ n)
  rw [← Real.exp_nat_mul] at hsp
  have hss : s ^ (2 ^ n) * s ^ (2 ^ n) ≤
      Real.exp ((2 * (2 ^ n : ℕ) * S) * t ^ (n + 2)) := by
    calc
      _ ≤ Real.exp ((2 ^ n : ℕ) * S) * Real.exp ((2 ^ n : ℕ) * S) :=
        mul_le_mul hsp hsp (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2 * (2 ^ n : ℕ) * S) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) htp)
  have hpE : (J : ℝ) * (B : ℝ) ^ (n + 1) + U ≤
      Real.exp (a * (b ^ (n + 1) + 1) * t ^ (n + 2)) :=
    hpoly.trans (by linarith [Real.add_one_le_exp (a * (b ^ (n + 1) + 1) * t ^ (n + 2))])
  calc
    _ ≤ Real.exp ((2 * (2 ^ n : ℕ) * S) * t ^ (n + 2)) *
        Real.exp (a * (b ^ (n + 1) + 1) * t ^ (n + 2)) :=
      mul_le_mul hss hpE (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring

end Ostmann

end OAI
