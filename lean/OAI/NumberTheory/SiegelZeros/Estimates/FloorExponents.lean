import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI


namespace SiegelZeros.W44

open scoped BigOperators

theorem floor_quotient_eq (a p : ℕ) : ⌊(a : ℝ) / p⌋₊ = a / p :=
  Nat.floor_div_eq_div a p

theorem quotient_lower (a p : ℕ) :
    (a : ℝ) / p - 1 ≤ (a / p : ℕ) := by
  simpa only [floor_quotient_eq] using (Nat.sub_one_lt_floor ((a : ℝ) / p)).le

theorem quotient_eq_zero_of_lt {a p : ℕ} (h : a < p) : a / p = 0 :=
  Nat.div_eq_of_lt h

def exponent {ι : Type*} (rows : Finset ι) (order : ι → ℕ) (p : ℕ) : ℕ :=
  ∑ i ∈ rows, order i / p

theorem exponent_lower {ι : Type*} (rows : Finset ι) (order : ι → ℕ) (p : ℕ) :
    (∑ i ∈ rows, (order i : ℝ)) / p - rows.card ≤ exponent rows order p := by
  have h := Finset.sum_le_sum (s := rows) (fun i _ => quotient_lower (order i) p)
  simpa only [exponent, Nat.cast_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem exponent_weight_interchange {ι : Type*} (rows : Finset ι) (order : ι → ℕ)
    (primes : Finset ℕ) (weight : ℕ → ℝ) :
    (∑ p ∈ primes, (exponent rows order p : ℝ) * weight p) =
      ∑ i ∈ rows, ∑ p ∈ primes, (order i / p : ℕ) * weight p := by
  simp only [exponent, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem weighted_exponent_lower {ι : Type*} (rows : Finset ι) (order : ι → ℕ)
    (primes : Finset ℕ) (weight : ℕ → ℝ)
    (hw : ∀ p ∈ primes, 0 ≤ weight p) :
    (∑ i ∈ rows, (order i : ℝ)) * (∑ p ∈ primes, weight p / p) -
      rows.card * (∑ p ∈ primes, weight p) ≤
        ∑ p ∈ primes, (exponent rows order p : ℝ) * weight p := by
  calc
    _ = ∑ p ∈ primes,
        ((∑ i ∈ rows, (order i : ℝ)) / p - rows.card) * weight p := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := Finset.sum_le_sum fun p hp =>
      mul_le_mul_of_nonneg_right (exponent_lower rows order p) (hw p hp)

theorem logarithmic_exponent_lower {ι : Type*} (rows : Finset ι) (order : ι → ℕ)
    (primes : Finset ℕ) (hp : ∀ p ∈ primes, 1 ≤ p) :
    (∑ i ∈ rows, (order i : ℝ)) * (∑ p ∈ primes, Real.log p / p) -
      rows.card * (∑ p ∈ primes, Real.log p) ≤
        ∑ p ∈ primes, (exponent rows order p : ℝ) * Real.log p := by
  apply weighted_exponent_lower
  intro p hmem
  apply Real.log_nonneg
  exact_mod_cast hp p hmem

theorem logarithmic_exponent_lower_subset {ι : Type*} (rows : Finset ι)
    (order : ι → ℕ) (good all : Finset ℕ) (hsub : good ⊆ all)
    (hp : ∀ p ∈ all, 1 ≤ p) :
    (∑ i ∈ rows, (order i : ℝ)) * (∑ p ∈ good, Real.log p / p) -
      rows.card * (∑ p ∈ all, Real.log p) ≤
        ∑ p ∈ good, (exponent rows order p : ℝ) * Real.log p := by
  have hsum : (∑ p ∈ good, Real.log (p : ℝ)) ≤ ∑ p ∈ all, Real.log (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hpa _
    apply Real.log_nonneg
    exact_mod_cast hp p hpa
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)) _).trans
    (logarithmic_exponent_lower rows order good (fun p h => hp p (hsub h)))

end SiegelZeros.W44

end OAI
