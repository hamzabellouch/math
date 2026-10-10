import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrands
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWWordDimensions

open scoped BigOperators Polynomial
open CWStrands

attribute [local instance] Classical.propDecidable

def sitePolynomial : Polynomial ℕ := 1 + Polynomial.C 5 * Polynomial.X + Polynomial.X ^ 2

theorem site_enumerator :
    (∑ a : Fin 7, (Polynomial.X : Polynomial ℕ) ^ CWLeafStatistics.weight a) =
      sitePolynomial := by
  norm_num [Fin.sum_univ_succ, CWLeafStatistics.weight, sitePolynomial]
  ring

theorem word_enumerator (P : Type*) [Fintype P] :
    (∑ w : P → Fin 7, (Polynomial.X : Polynomial ℕ) ^ weight w) =
      sitePolynomial ^ Fintype.card P := by
  classical
  calc
    (∑ w : P → Fin 7, (Polynomial.X : Polynomial ℕ) ^ weight w) =
        ∑ w : P → Fin 7, ∏ i, (Polynomial.X : Polynomial ℕ) ^
          CWLeafStatistics.weight (w i) := by
      apply Finset.sum_congr rfl
      intro w _
      exact (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i => CWLeafStatistics.weight (w i)) Polynomial.X).symm
    _ = ∏ _i : P, ∑ a : Fin 7, (Polynomial.X : Polynomial ℕ) ^
        CWLeafStatistics.weight a :=
      (Fintype.prod_sum (fun (_i : P) (a : Fin 7) =>
        (Polynomial.X : Polynomial ℕ) ^ CWLeafStatistics.weight a)).symm
    _ = sitePolynomial ^ Fintype.card P := by simp only [site_enumerator, Finset.prod_const,
      Finset.card_univ]

abbrev WeightWords (P : Type*) [Fintype P] (j : ℕ) := {w : P → Fin 7 // weight w = j}

theorem card_weightWords (P : Type*) [Fintype P] (j : ℕ) :
    Fintype.card (WeightWords P j) = (sitePolynomial ^ Fintype.card P).coeff j := by
  classical
  rw [← word_enumerator]
  simp [WeightWords, Fintype.card_subtype, Polynomial.coeff_X_pow, eq_comm]

def recursiveCoeff : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j => recursiveCoeff n j +
      5 * (if 1 ≤ j then recursiveCoeff n (j - 1) else 0) +
      (if 2 ≤ j then recursiveCoeff n (j - 2) else 0)

theorem coeff_eq_recursive (n j : ℕ) :
    (sitePolynomial ^ n).coeff j = recursiveCoeff n j := by
  induction n generalizing j with
  | zero => simp [recursiveCoeff, Polynomial.coeff_one]
  | succ n ih =>
    have hmul (p : Polynomial ℕ) : sitePolynomial * p =
        p + Polynomial.C 5 * (Polynomial.X * p) + Polynomial.X ^ 2 * p := by
      simp only [sitePolynomial, add_mul, one_mul, mul_assoc]
    have hshift := Polynomial.coeff_X_pow_mul' (sitePolynomial ^ n) 1 j
    simp only [pow_one] at hshift
    rw [pow_succ', hmul, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, hshift, Polynomial.coeff_X_pow_mul']
    simp only [ih, recursiveCoeff]

theorem card_weightWords_fin (n j : ℕ) :
    Fintype.card (WeightWords (Fin n) j) = recursiveCoeff n j := by
  have h := card_weightWords (Fin n) j
  simp only [Fintype.card_fin, coeff_eq_recursive] at h
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact h

end MatrixMultiplication.CWWordDimensions

end

end OAI
