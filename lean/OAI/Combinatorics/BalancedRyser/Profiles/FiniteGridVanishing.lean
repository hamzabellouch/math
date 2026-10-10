import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace OAI

namespace Balanced.StabilityPolynomial

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

open Polynomial in

theorem field_polynomial_prod :
    (∏ a : K, (Polynomial.X - Polynomial.C a)) =
      (Polynomial.X : K[X]) ^ Fintype.card K - Polynomial.X := by
  classical
  have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K)
  have hr : (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).roots.card =
      (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
    exact Finset.card_univ
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hr
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  exact h

open MvPolynomial

theorem field_coordinate_prod {σ : Type*} (i : σ) :
    (∏ a : K, (X i - C a)) = (X i : MvPolynomial σ K) ^ Fintype.card K - X i := by
  classical
  have h := congrArg (Polynomial.eval₂RingHom (C : K →+* MvPolynomial σ K) (X i))
    (field_polynomial_prod (K := K))
  simpa using h

theorem field_coordinate_totalDegree {σ : Type*} (i : σ) :
    ((X i : MvPolynomial σ K) ^ Fintype.card K - X i).totalDegree =
      Fintype.card K := by
  rw [sub_eq_add_neg,
    totalDegree_add_eq_left_of_totalDegree_lt (show
      (- (X i : MvPolynomial σ K)).totalDegree <
        ((X i : MvPolynomial σ K) ^ Fintype.card K).totalDegree by
          simpa using (Fintype.one_lt_card : 1 < Fintype.card K))]
  exact totalDegree_X_pow _ _

theorem field_coordinate_ne_zero {σ : Type*} (i : σ) :
    (X i : MvPolynomial σ K) ^ Fintype.card K - X i ≠ 0 := by
  intro h
  have hdeg := congrArg totalDegree h
  rw [field_coordinate_totalDegree, totalDegree_zero] at hdeg
  exact Fintype.card_ne_zero hdeg

theorem finite_grid_decomposition {σ : Type*} [Fintype σ]
    (H : MvPolynomial σ K) (hH : ∀ x : σ → K, eval x H = 0) :
    ∃ G : σ → MvPolynomial σ K,
      (∀ i, (((X i) ^ Fintype.card K - X i) * G i).totalDegree ≤ H.totalDegree) ∧
      H = ∑ i, ((X i) ^ Fintype.card K - X i) * G i := by
  classical
  obtain ⟨G, hdeg, heq⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ : σ => Finset.univ) (fun _ => Finset.univ_nonempty)
    H (fun x _ => hH x)
  refine ⟨G, ?_, ?_⟩
  · intro i
    simpa only [field_coordinate_prod] using hdeg i
  · rw [heq, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_fintype G (fun i a => a • ∏ r : K, (X i - C r))
      (fun _ => zero_smul _ _)]
    simp only [smul_eq_mul, field_coordinate_prod, mul_comm]

theorem finite_grid_decomposition_degree {σ : Type*} [Fintype σ]
    (H : MvPolynomial σ K) (hH : ∀ x : σ → K, eval x H = 0) :
    ∃ G : σ → MvPolynomial σ K,
      (∀ i, (G i).totalDegree ≤ H.totalDegree - Fintype.card K) ∧
      H = ∑ i, ((X i) ^ Fintype.card K - X i) * G i := by
  obtain ⟨G, hdeg, heq⟩ := finite_grid_decomposition H hH
  refine ⟨G, ?_, heq⟩
  intro i
  by_cases hGi : G i = 0
  · simp [hGi]
  · have hd := hdeg i
    rw [totalDegree_mul_of_isDomain (field_coordinate_ne_zero i) hGi,
      field_coordinate_totalDegree] at hd
    omega

theorem bivariate_grid_decomposition
    (H : MvPolynomial (Fin 2) K)
    (hH : ∀ x : Fin 2 → K, eval x H = 0) :
    ∃ f g : MvPolynomial (Fin 2) K,
      (((X 0) ^ Fintype.card K - X 0) * f).totalDegree ≤ H.totalDegree ∧
      (((X 1) ^ Fintype.card K - X 1) * g).totalDegree ≤ H.totalDegree ∧
      H = ((X 0) ^ Fintype.card K - X 0) * f +
        ((X 1) ^ Fintype.card K - X 1) * g := by
  obtain ⟨G, hdeg, heq⟩ := finite_grid_decomposition H hH
  exact ⟨G 0, G 1, hdeg 0, hdeg 1, by simpa only [Fin.sum_univ_two] using heq⟩

theorem bivariate_grid_decomposition_degree
    (H : MvPolynomial (Fin 2) K)
    (hH : ∀ x : Fin 2 → K, eval x H = 0) :
    ∃ f g : MvPolynomial (Fin 2) K,
      f.totalDegree ≤ H.totalDegree - Fintype.card K ∧
      g.totalDegree ≤ H.totalDegree - Fintype.card K ∧
      H = ((X 0) ^ Fintype.card K - X 0) * f +
        ((X 1) ^ Fintype.card K - X 1) * g := by
  obtain ⟨G, hdeg, heq⟩ := finite_grid_decomposition_degree H hH
  exact ⟨G 0, G 1, hdeg 0, hdeg 1, by simpa only [Fin.sum_univ_two] using heq⟩

end Balanced.StabilityPolynomial

end OAI
