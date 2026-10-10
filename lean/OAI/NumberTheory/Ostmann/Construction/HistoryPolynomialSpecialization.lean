import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.BigOperators
import OAI.NumberTheory.Ostmann.Characters.PolynomialGiantRows

namespace OAI

/-! # Actual cleared history polynomials with one prime left variable -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def specializeHistoryVariable {σ : Type*}
    (a : σ → ℝ) (i : σ) : MvPolynomial σ ℤ →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (Int.castRingHom ℝ))
    (fun j => if j = i then Polynomial.X else Polynomial.C (a j))

theorem specializeHistoryVariable_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (x : ℝ) :
    (specializeHistoryVariable a i P).eval x =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P := by
  unfold specializeHistoryVariable
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom x).comp (Polynomial.C.comp (Int.castRingHom ℝ)) =
      Int.castRingHom ℝ := by ext z; simp
  rw [hc]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj, Function.update]

/-- Fixing all the other prime variables cannot increase the degree. The
bound comes from the original monomial support, so cancellation is harmless. -/
theorem specializeHistoryVariable_natDegree {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) :
    (specializeHistoryVariable a i P).natDegree ≤ P.totalDegree := by
  let v : σ → Polynomial ℝ := fun j => if j = i then Polynomial.X else Polynomial.C (a j)
  have hv (j : σ) : (v j).natDegree ≤ 1 := by
    dsimp only [v]
    split_ifs <;> simp
  have hs : specializeHistoryVariable a i P =
      ∑ d ∈ P.support, specializeHistoryVariable a i (MvPolynomial.monomial d (P.coeff d)) := by
    rw [← map_sum]
    exact congrArg (specializeHistoryVariable a i) P.as_sum
  rw [hs]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hp : (d.prod fun j k => v j ^ k).natDegree ≤ d.sum (fun _ k => k) := by
    change (∏ j ∈ d.support, v j ^ d j).natDegree ≤ ∑ j ∈ d.support, d j
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    apply Finset.sum_le_sum
    intro j _
    exact (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (d j) (hv j))).trans_eq (Nat.mul_one _)
  simp only [specializeHistoryVariable, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_monomial, RingHom.comp_apply]
  change ((Polynomial.C (P.coeff d : ℝ)) * d.prod (fun j k => v j ^ k)).natDegree ≤ _
  calc
    _ ≤ (Polynomial.C (P.coeff d : ℝ)).natDegree + (d.prod fun j k => v j ^ k).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + d.sum (fun _ k => k) := by simpa only [Polynomial.natDegree_C, zero_add] using hp
    _ ≤ P.totalDegree := by simpa only [zero_add] using MvPolynomial.le_totalDegree hd

noncomputable def normalizedHistoryPolynomial {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d : ℝ) : Polynomial ℝ :=
  Polynomial.C d⁻¹ * specializeHistoryVariable a i P

theorem normalizedHistoryPolynomial_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d x : ℝ) :
    (normalizedHistoryPolynomial P a i d).eval x =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d := by
  simp only [normalizedHistoryPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    specializeHistoryVariable_eval, div_eq_mul_inv]
  ring

theorem normalizedHistoryPolynomial_natDegree {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d : ℝ) :
    (normalizedHistoryPolynomial P a i d).natDegree ≤ P.totalDegree := by
  exact (Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_C, zero_add] using specializeHistoryVariable_natDegree P a i))

end Ostmann

end OAI
