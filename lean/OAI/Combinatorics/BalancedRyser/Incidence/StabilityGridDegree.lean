import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Combinatorics.Nullstellensatz
import OAI.Combinatorics.BalancedRyser.Incidence.FiniteGridPolynomial

namespace OAI

namespace Balanced.StabilityPolynomial

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F]

private theorem finiteField_factorization :
    (∏ a : F, (Polynomial.X - Polynomial.C a)) =
      (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial F) := by
  classical
  let p : Polynomial F := Polynomial.X ^ Fintype.card F - Polynomial.X
  have hp : p.Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast (Fintype.one_lt_card (α := F))
  have hr : p.roots = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X F
  have hd : p.natDegree = Fintype.card F :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp
    (by rw [hr, hd]; rfl)
  rw [hr] at h
  exact h

theorem finiteField_coordinate_factorization {σ : Type*} (i : σ) :
    (∏ a : F, (MvPolynomial.X i - MvPolynomial.C a)) =
      (MvPolynomial.X i ^ Fintype.card F - MvPolynomial.X i : MvPolynomial σ F) := by
  have h := congrArg (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ F))
    (finiteField_factorization (F := F))
  simpa using h

theorem finite_grid_decomposition_totalDegree {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ F) (hP : ∀ x : σ → F, MvPolynomial.eval x P = 0) :
    ∃ A : σ → MvPolynomial σ F,
      P = ∑ i, (MvPolynomial.X i ^ Fintype.card F - MvPolynomial.X i) * A i ∧
      ∀ i, ((MvPolynomial.X i ^ Fintype.card F - MvPolynomial.X i) * A i).totalDegree ≤
        P.totalDegree := by
  classical
  obtain ⟨A, hd, heq⟩ := MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination
    (fun _ : σ => (Finset.univ : Finset F))
    (fun _ => Finset.univ_nonempty) P (fun x _ => hP x)
  refine ⟨A, ?_, ?_⟩
  · rw [heq, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (by intro i; simp)]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_eq_mul, finiteField_coordinate_factorization]
    exact mul_comm _ _
  · intro i
    simpa only [finiteField_coordinate_factorization] using hd i

theorem finiteField_coordinate_totalDegree {σ : Type*} (i : σ) :
    (MvPolynomial.X i ^ Fintype.card F - MvPolynomial.X i :
      MvPolynomial σ F).totalDegree = Fintype.card F := by
  rw [sub_eq_add_neg, MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · exact MvPolynomial.totalDegree_X_pow i _
  · simpa using (Fintype.one_lt_card (α := F))

theorem finite_grid_decomposition_multiplier_degree {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ F) (hP : ∀ x : σ → F, MvPolynomial.eval x P = 0) :
    ∃ A : σ → MvPolynomial σ F,
      P = ∑ i, (MvPolynomial.X i ^ Fintype.card F - MvPolynomial.X i) * A i ∧
      ∀ i, (A i).totalDegree ≤ P.totalDegree - Fintype.card F := by
  obtain ⟨A, heq, hd⟩ := finite_grid_decomposition_totalDegree P hP
  refine ⟨A, heq, ?_⟩
  intro i
  by_cases ha : A i = 0
  · simp [ha]
  · have hg := finiteField_coordinate_totalDegree (F := F) i
    have hne : (MvPolynomial.X i ^ Fintype.card F - MvPolynomial.X i :
        MvPolynomial σ F) ≠ 0 := by
      intro hz
      rw [hz, MvPolynomial.totalDegree_zero] at hg
      exact Fintype.card_ne_zero hg.symm
    have hi := hd i
    rw [MvPolynomial.totalDegree_mul_of_isDomain hne ha, hg] at hi
    omega

theorem bivariate_grid_decomposition_degree_bounds
    (P : MvPolynomial (Fin 2) F)
    (hP : ∀ x : Fin 2 → F, MvPolynomial.eval x P = 0) :
    ∃ A B : MvPolynomial (Fin 2) F,
      P = (MvPolynomial.X 0 ^ Fintype.card F - MvPolynomial.X 0) * A +
        (MvPolynomial.X 1 ^ Fintype.card F - MvPolynomial.X 1) * B ∧
      A.totalDegree ≤ P.totalDegree - Fintype.card F ∧
      B.totalDegree ≤ P.totalDegree - Fintype.card F := by
  obtain ⟨A, heq, hd⟩ := finite_grid_decomposition_multiplier_degree P hP
  exact ⟨A 0, A 1, by simpa only [Fin.sum_univ_two] using heq, hd 0, hd 1⟩

end Balanced.StabilityPolynomial

end OAI
