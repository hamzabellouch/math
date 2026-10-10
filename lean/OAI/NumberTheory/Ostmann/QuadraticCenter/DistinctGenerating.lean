import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators Polynomial
open Polynomial

noncomputable def distinctGenerating {ι : Type*} (I : Finset ι) (y : ι → ℤ) : ℝ[X] :=
  ∏ i ∈ I, (1 + C (y i : ℝ) * X)

theorem distinctGenerating_eq_powerset {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ) :
    distinctGenerating I y =
      ∑ s ∈ I.powerset, C (∏ i ∈ s, (y i : ℝ)) * X ^ s.card := by
  have h := Finset.prod_add (fun i => C (y i : ℝ) * (X : ℝ[X])) (fun _ => 1) I
  simpa only [distinctGenerating, add_comm (1 : ℝ[X]),
    Finset.prod_mul_distrib, Finset.prod_const, one_pow, mul_one, map_prod] using h

theorem distinctGenerating_coeff {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ) (k : ℕ) :
    (distinctGenerating I y).coeff k =
      ∑ s ∈ I.powersetCard k, ∏ i ∈ s, (y i : ℝ) := by
  rw [distinctGenerating_eq_powerset, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  congr 1
  ext s
  simp [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powerset, eq_comm]

theorem distinctGenerating_sign_counts {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1) :
    distinctGenerating I y =
      (1 + X) ^ (I.filter (fun i => y i = 1)).card *
        (1 - X) ^ (I.filter (fun i => y i = -1)).card := by
  induction I using Finset.induction_on with
  | empty => simp [distinctGenerating]
  | @insert a I ha ih =>
    have hyI : ∀ i ∈ I, y i = -1 ∨ y i = 0 ∨ y i = 1 :=
      fun i hi => hy i (Finset.mem_insert_of_mem hi)
    rcases hy a (Finset.mem_insert_self _ _) with h | h | h
    · simp only [distinctGenerating, Finset.prod_insert ha]
      rw [show (∏ i ∈ I, (1 + C (y i : ℝ) * X)) = distinctGenerating I y by rfl,
        ih hyI]
      simp [Finset.filter_insert, h, ha, pow_succ]
      ring
    · simpa [distinctGenerating, Finset.prod_insert ha, h, Finset.filter_insert]
        using ih hyI
    · simp only [distinctGenerating, Finset.prod_insert ha]
      rw [show (∏ i ∈ I, (1 + C (y i : ℝ) * X)) = distinctGenerating I y by rfl,
        ih hyI]
      simp [Finset.filter_insert, h, ha, pow_succ]
      ring

theorem sign_count_pairing (p m : ℕ) (hm : m ≤ p) :
    ((1 + X : ℝ[X]) ^ p) * (1 - X) ^ m =
      (1 + X) ^ (p - m) * (1 - X ^ 2) ^ m := by
  calc
    _ = (1 + X : ℝ[X]) ^ (p - m) * ((1 + X : ℝ[X]) ^ m * (1 - X : ℝ[X]) ^ m) := by
      nth_rw 1 [show p = (p - m) + m by omega]
      rw [pow_add]
      ring
    _ = _ := by
      rw [← mul_pow, show (1 + X : ℝ[X]) * (1 - X) = 1 - X ^ 2 by ring]

theorem even_generating_expansion (m : ℕ) :
    (1 - X ^ 2 : ℝ[X]) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        C ((-1 : ℝ) ^ j * (m.choose j : ℝ)) * X ^ (2 * j) := by
  rw [show (1 - X ^ 2 : ℝ[X]) = -X ^ 2 + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [one_pow, mul_one, ← pow_mul, map_mul, map_pow,
    map_neg, map_one, map_natCast]
  ring

theorem paired_generating_coeff (S m k : ℕ) :
    (((1 + X : ℝ[X]) ^ S) * (1 - X ^ 2) ^ m).coeff k =
      ∑ j ∈ Finset.range (m + 1),
        if 2 * j ≤ k then
          (-1 : ℝ) ^ j * (m.choose j : ℝ) * (S.choose (k - 2 * j) : ℝ)
        else 0 := by
  rw [even_generating_expansion, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_one_add_X_pow]
    ring
  · rfl

end Ostmann.QuadraticCenter

end OAI
