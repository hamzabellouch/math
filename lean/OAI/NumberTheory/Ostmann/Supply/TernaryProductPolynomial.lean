import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination
import OAI.NumberTheory.Ostmann.Construction.DistinctTupleProducts

namespace OAI

/-! # The generating polynomial for a finite ternary population

The differential equation below yields an elementary repeat-removal bound.
It uses only `y^3 = y`, the identity satisfied by the oriented quadratic
characters, and does not invoke partition inversion as an additional input.
-/

namespace Ostmann

open scoped BigOperators Classical
open Polynomial

noncomputable def ternaryProduct {A : Type*} (S : Finset A) (y : A → ℝ) : ℝ[X] :=
  ∏ i ∈ S, (1 + C (y i) * X)

theorem ternaryProduct_coeff {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (k : ℕ) :
    (ternaryProduct S y).coeff k = ∑ T ∈ S.powersetCard k, ∏ i ∈ T, y i := by
  have hexp : ternaryProduct S y =
      ∑ T ∈ S.powerset, C (∏ i ∈ T, y i) * X ^ T.card := by
    unfold ternaryProduct
    simp_rw [add_comm (1 : ℝ[X])]
    rw [Finset.prod_add_one]
    apply Finset.sum_congr rfl
    intro T _
    simp only [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const]
  rw [hexp, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  simp only [eq_comm]

theorem distinct_tuple_product_coeff {A : Type*} [Fintype A] [DecidableEq A]
    (y : A → ℝ) (k : ℕ) :
    (∑ e : Fin k ↪ A, ∏ i, y (e i)) =
      (k.factorial : ℝ) * (ternaryProduct Finset.univ y).coeff k := by
  rw [ternaryProduct_coeff, distinct_tuple_sum]

theorem ternaryProduct_differential {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (hy : ∀ i ∈ S, (y i) ^ 3 = y i) :
    (1 - X ^ 2) * derivative (ternaryProduct S y) =
      (C (∑ i ∈ S, y i) - C (∑ i ∈ S, (y i) ^ 2) * X) * ternaryProduct S y := by
  have hterm (i : A) (hi : i ∈ S) :
      (1 - X ^ 2) * C (y i) =
        (C (y i) - C ((y i) ^ 2) * X) * (1 + C (y i) * X) := by
    have hc : C (y i) ^ 3 = (C (y i) : ℝ[X]) := by rw [← map_pow, hy i hi]
    simp only [map_pow]
    linear_combination X ^ 2 * hc
  unfold ternaryProduct
  rw [derivative_prod_finset, Finset.mul_sum]
  calc
    _ = ∑ i ∈ S, (C (y i) - C ((y i) ^ 2) * X) *
        ∏ j ∈ S, (1 + C (y j) * X) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [derivative_add, derivative_one, derivative_mul, derivative_C,
        zero_mul, derivative_X, mul_one, zero_add]
      rw [show (1 - X ^ 2) * ((∏ j ∈ S.erase i, (1 + C (y j) * X)) * C (y i)) =
          ((1 - X ^ 2) * C (y i)) * ∏ j ∈ S.erase i, (1 + C (y j) * X) by ring,
        hterm i hi, mul_assoc, Finset.mul_prod_erase S (fun j => (1 + C (y j) * X : ℝ[X])) hi]
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum]

theorem ternaryProduct_coeff_recurrence {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (hy : ∀ i ∈ S, (y i) ^ 3 = y i) (n : ℕ) :
    ((n + 2 : ℕ) : ℝ) * (ternaryProduct S y).coeff (n + 2) =
      (∑ i ∈ S, y i) * (ternaryProduct S y).coeff (n + 1) -
      ((∑ i ∈ S, (y i) ^ 2) - n) * (ternaryProduct S y).coeff n := by
  have h := congrArg (fun p : ℝ[X] => p.coeff (n + 1))
    (ternaryProduct_differential S y hy)
  simp only [sub_mul, one_mul, coeff_sub, coeff_derivative, coeff_C_mul] at h
  have hx : (X ^ 2 * derivative (ternaryProduct S y)).coeff (n + 1) =
      n * (ternaryProduct S y).coeff n := by
    cases n with
    | zero => simp [coeff_X_pow_mul']
    | succ n =>
      rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul]
      simp only [coeff_derivative]
      push_cast
      ring
  have hx' : (C (∑ i ∈ S, (y i) ^ 2) * X * ternaryProduct S y).coeff (n + 1) =
      (∑ i ∈ S, (y i) ^ 2) * (ternaryProduct S y).coeff n := by
    rw [mul_assoc, coeff_C_mul, coeff_X_mul]
  rw [hx, hx'] at h
  push_cast at h ⊢
  nlinarith only [h]

noncomputable def ternaryDistinct {A : Type*} (S : Finset A) (y : A → ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (ternaryProduct S y).coeff k

@[simp] theorem ternaryDistinct_zero {A : Type*} (S : Finset A) (y : A → ℝ) :
    ternaryDistinct S y 0 = 1 := by
  simp [ternaryDistinct, ternaryProduct, coeff_zero_prod]

@[simp] theorem ternaryDistinct_one {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) :
    ternaryDistinct S y 1 = ∑ i ∈ S, y i := by
  rw [ternaryDistinct, ternaryProduct_coeff]
  simp [Finset.powersetCard_one]

theorem ternaryDistinct_recurrence {A : Type*} [DecidableEq A]
    (S : Finset A) (y : A → ℝ) (hy : ∀ i ∈ S, (y i) ^ 3 = y i) (n : ℕ) :
    ternaryDistinct S y (n + 2) =
      (∑ i ∈ S, y i) * ternaryDistinct S y (n + 1) -
      (n + 1) * ((∑ i ∈ S, (y i) ^ 2) - n) * ternaryDistinct S y n := by
  have h := ternaryProduct_coeff_recurrence S y hy n
  push_cast at h
  unfold ternaryDistinct
  rw [show (n + 2).factorial = (n + 2) * (n + 1).factorial from Nat.factorial_succ (n + 1)]
  push_cast
  rw [mul_assoc, mul_left_comm ((n : ℝ) + 2), h, Nat.factorial_succ]
  push_cast
  ring

end Ostmann

end OAI
