import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.Positivity
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # Weighted polynomial root bounds for the arithmetic priors -/

namespace Ostmann

open scoped BigOperators

theorem weighted_univariate_roots_le {A : Type*} [Fintype A]
    (value : A → ℚ) (hinj : Function.Injective value) (P : Polynomial ℚ) (hP : P ≠ 0)
    (μ : A → ℝ) (α : ℝ) (hα : 0 ≤ α) (hμ : ∀ a, μ a ≤ α) :
    (∑ a : A, if P.eval (value a) = 0 then μ a else 0) ≤ (P.natDegree : ℝ) * α := by
  classical
  let S := Finset.univ.filter fun a => P.eval (value a) = 0
  have hc : S.card ≤ P.natDegree := by
    apply (Finset.card_le_card_of_injOn value (t := P.roots.toFinset) ?_ hinj.injOn).trans
      (P.roots.toFinset_card_le.trans P.card_roots')
    intro a ha
    change value a ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact (Finset.mem_filter.mp ha).2
  calc
    _ = ∑ a ∈ S, μ a := (Finset.sum_filter _ _).symm
    _ ≤ ∑ _a ∈ S, α := Finset.sum_le_sum fun a _ => hμ a
    _ = (S.card : ℝ) * α := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hα

/-- The arithmetic polynomial estimate for independent, possibly unequal finite priors. -/
theorem weighted_polynomial_roots_le {A : Type*} [Fintype A]
    (value : A → ℚ) (hinj : Function.Injective value) (α : ℝ) (hα : 0 ≤ α) :
    ∀ {n : ℕ} (P : MvPolynomial (Fin n) ℚ), P ≠ 0 →
      ∀ μ : Fin n → A → ℝ,
      (∀ i a, 0 ≤ μ i a) → (∀ i, ∑ a, μ i a = 1) → (∀ i a, μ i a ≤ α) →
      (∑ x : Fin n → A, productPrior μ x *
        (if MvPolynomial.eval (fun i => value (x i)) P = 0 then 1 else 0)) ≤
          (P.totalDegree : ℝ) * α := by
  classical
  intro n
  induction n with
  | zero =>
    intro P hP μ _ _ _
    have hc : P.coeff 0 ≠ 0 := by
      intro h
      apply hP
      rw [P.eq_C_of_isEmpty, h, map_zero]
    have he (x : Fin 0 → A) : MvPolynomial.eval (fun i => value (x i)) P ≠ 0 := by
      rw [P.eq_C_of_isEmpty, MvPolynomial.eval_C]
      exact hc
    simp only [he, ite_false, mul_zero, Finset.sum_const_zero]
    positivity
  | succ n ih =>
    intro P hP μ hμ hmass hmax
    let Q := MvPolynomial.finSuccEquiv ℚ n P
    let d := Q.natDegree
    let L := Q.leadingCoeff
    have hQ : Q ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hP
    have hL : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have hdegree : L.totalDegree + d ≤ P.totalDegree := by
      exact MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P d (by
        change Q.coeff Q.natDegree ≠ 0
        exact hL)
    let μtail : Fin n → A → ℝ := fun i => μ i.succ
    let F (x : Fin n → A) :=
      if MvPolynomial.eval (fun i => value (x i)) L = 0 then (1 : ℝ) else 0
    have hinner (x : Fin n → A) :
        (∑ a : A, μ 0 a *
          (if MvPolynomial.eval (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) P = 0 then 1 else 0)) ≤
            F x + (d : ℝ) * α := by
      by_cases hx : MvPolynomial.eval (fun i => value (x i)) L = 0
      · have hsum : (∑ a : A, μ 0 a *
            (if MvPolynomial.eval (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) P = 0 then 1 else 0)) ≤ 1 := by
          apply le_trans ?_ (le_of_eq (hmass 0))
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact le_of_eq (mul_one _)
          · simpa only [mul_zero] using hμ 0 a
        exact hsum.trans (by
          simp only [F, hx, ite_true]
          exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hα))
      · let q : Polynomial ℚ := Q.map (MvPolynomial.eval (fun i => value (x i)))
        have hqd : q.natDegree = d :=
          Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hx
        have hq : q ≠ 0 := by
          intro hz
          apply hx
          change (MvPolynomial.eval (fun i => value (x i))) (Q.coeff d) = 0
          rw [← Polynomial.coeff_map, show Q.map (MvPolynomial.eval (fun i => value (x i))) = q from rfl,
            hz, Polynomial.coeff_zero]
        have he (a : A) : MvPolynomial.eval (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) P = q.eval (value a) := by
          have hc : (fun i => value ((Fin.cons a x : Fin (n + 1) → A) i)) =
              Fin.cons (value a) (fun i => value (x i)) := by
            funext i
            refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
          rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
        simp_rw [he, mul_ite, mul_one, mul_zero]
        simpa only [F, hx, ite_false, zero_add, hqd] using
          weighted_univariate_roots_le value hinj q hq (μ 0) α hα (hmax 0)
    rw [sum_productPrior_cons]
    calc
      _ ≤ ∑ x : Fin n → A, productPrior μtail x * (F x + (d : ℝ) * α) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hinner x)
          (productPrior_nonneg μtail (fun i => hμ i.succ) x)
      _ = (∑ x : Fin n → A, productPrior μtail x * F x) + (d : ℝ) * α := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [productPrior_mass μtail (fun i => hmass i.succ), one_mul]
      _ ≤ (L.totalDegree : ℝ) * α + (d : ℝ) * α :=
        add_le_add (ih L hL μtail (fun i => hμ i.succ)
          (fun i => hmass i.succ) (fun i => hmax i.succ)) le_rfl
      _ ≤ _ := by
        rw [← add_mul, ← Nat.cast_add]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) hα

end Ostmann

end OAI
