import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorCorrelationEuler

namespace OAI

/-! # Numerical Euler-product constants for the large-kernel coefficient energy -/

namespace Ostmann

open scoped BigOperators

/-- A fixed lower cutoff for the small primes suffices for the manuscript's
`.006 K` low-weight norm estimate. No asymptotic prime estimate is assumed. -/
theorem low_weight_euler_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 10000 ≤ p) :
    Real.exp ((P.card : ℝ) / 200) *
      (∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) ≤
        Real.exp (3 * (P.card : ℝ) / 250) := by
  have hlocal (p : ℕ) (hp : p ∈ P) :
      (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹) ≤
        Real.exp (7 / 1000 : ℝ) := by
    have hpR : (10000 : ℝ) ≤ p := by exact_mod_cast hP p hp
    have hs : (100 : ℝ) ≤ Real.sqrt (p : ℝ) := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ)]
    have hi : (Real.sqrt (p : ℝ))⁻¹ ≤ (100 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hs
    have hb : (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ≤ 7 / 1000 := by
      norm_num at hi ⊢
      linarith
    have hex := Real.add_one_le_exp (7 / 1000 : ℝ)
    linarith
  calc
    _ ≤ Real.exp ((P.card : ℝ) / 200) * ∏ _p ∈ P, Real.exp (7 / 1000 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact Finset.prod_le_prod₀ (fun p hp => by positivity) hlocal
    _ = Real.exp (3 * (P.card : ℝ) / 250) := by
      rw [← Real.exp_sum, Finset.sum_const, nsmul_eq_mul, ← Real.exp_add]
      congr 1
      ring

theorem low_weight_euler_norm_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 10000 ≤ p) :
    Real.sqrt (Real.exp ((P.card : ℝ) / 200) *
      (∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹))) ≤
        Real.exp (3 * (P.card : ℝ) / 500) := by
  apply (Real.sqrt_le_sqrt (low_weight_euler_bound P hP)).trans_eq
  rw [← Real.exp_half]
  congr 1
  ring

theorem low_weight_euler_bound_scale (P : Finset ℕ) (hP : ∀ p ∈ P, 10000 ≤ p)
    (K : ℝ) (hK : (P.card : ℝ) ≤ K) :
    Real.exp (K / 200) *
      (∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) ≤
        Real.exp (3 * K / 250) := by
  calc
    _ = Real.exp ((K - P.card) / 200) * (Real.exp ((P.card : ℝ) / 200) *
        ∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp ((K - P.card) / 200) * Real.exp (3 * (P.card : ℝ) / 250) :=
      mul_le_mul_of_nonneg_left (low_weight_euler_bound P hP) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith

/-- The coarser small-kernel divisor factor is still harmless compared with
its `exp(-.9 K)` loss. -/
theorem small_kernel_divisor_product_bound (K : ℕ) :
    (1 + Real.sqrt 2 / 16) ^ K ≤ Real.exp ((K : ℝ) / 10) := by
  have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlocal : 1 + Real.sqrt 2 / 16 ≤ Real.exp (1 / 10 : ℝ) := by
    apply le_trans _ (Real.add_one_le_exp (1 / 10 : ℝ))
    linarith
  calc
    _ ≤ (Real.exp (1 / 10 : ℝ)) ^ K := pow_le_pow_left₀ (by positivity) hlocal K
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end Ostmann

end OAI
