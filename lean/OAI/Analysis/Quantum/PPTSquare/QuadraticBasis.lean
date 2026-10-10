import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped BigOperators
open MvPolynomial
namespace QuadraticBasis

def powers : Fin 10 → Fin 4 → ℕ :=
  ![![2,0,0,0],![1,0,0,1],![1,0,1,0],![1,1,0,0],![0,0,0,2],
    ![0,0,1,1],![0,0,2,0],![0,1,0,1],![0,1,1,0],![0,2,0,0]]
def exponent (j : Fin 10) : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm (powers j)
lemma exponent_apply (j : Fin 10) (i : Fin 4) : exponent j i = powers j i := by rfl
lemma exponent_inj : Function.Injective exponent := by
  have hp : Function.Injective powers := by decide
  intro i j hh
  apply hp
  ext a
  exact congrArg (fun f : Fin 4 →₀ ℕ => f a) hh
lemma degree_two (j : Fin 10) : (exponent j).degree = 2 := by
  rw [Finsupp.degree_eq_sum]
  change ∑ i : Fin 4, powers j i = 2
  revert j
  decide

lemma exponents_exhaust (d : Fin 4 →₀ ℕ) (hd : d.degree = 2) : ∃ j, exponent j = d := by
  have hs : d 0 + d 1 + d 2 + d 3 = 2 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc] using hd
  have cases : (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 0) ∨
      (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 1) ∨
      (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1 ∧ d 3 = 0) ∨
      (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0 ∧ d 3 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 2) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1 ∧ d 3 = 1) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2 ∧ d 3 = 0) ∨
      (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0 ∧ d 3 = 1) ∨
      (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1 ∧ d 3 = 0) ∨
      (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0 ∧ d 3 = 0) := by
    have h0 : d 0 ≤ 2 := by omega
    have h1 : d 1 ≤ 2 := by omega
    have h2 : d 2 ≤ 2 := by omega
    interval_cases h0v : d 0 <;> interval_cases h1v : d 1 <;> interval_cases h2v : d 2 <;> simp_all <;> omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · refine ⟨0, ?_⟩
    ext a
    fin_cases a
    · change 2 = d 0
      exact h0.1.symm
    · change 0 = d 1
      exact h0.2.1.symm
    · change 0 = d 2
      exact h0.2.2.1.symm
    · change 0 = d 3
      exact h0.2.2.2.symm
  · refine ⟨1, ?_⟩
    ext a
    fin_cases a
    · change 1 = d 0
      exact h1.1.symm
    · change 0 = d 1
      exact h1.2.1.symm
    · change 0 = d 2
      exact h1.2.2.1.symm
    · change 1 = d 3
      exact h1.2.2.2.symm
  · refine ⟨2, ?_⟩
    ext a
    fin_cases a
    · change 1 = d 0
      exact h2.1.symm
    · change 0 = d 1
      exact h2.2.1.symm
    · change 1 = d 2
      exact h2.2.2.1.symm
    · change 0 = d 3
      exact h2.2.2.2.symm
  · refine ⟨3, ?_⟩
    ext a
    fin_cases a
    · change 1 = d 0
      exact h3.1.symm
    · change 1 = d 1
      exact h3.2.1.symm
    · change 0 = d 2
      exact h3.2.2.1.symm
    · change 0 = d 3
      exact h3.2.2.2.symm
  · refine ⟨4, ?_⟩
    ext a
    fin_cases a
    · change 0 = d 0
      exact h4.1.symm
    · change 0 = d 1
      exact h4.2.1.symm
    · change 0 = d 2
      exact h4.2.2.1.symm
    · change 2 = d 3
      exact h4.2.2.2.symm
  · refine ⟨5, ?_⟩
    ext a
    fin_cases a
    · change 0 = d 0
      exact h5.1.symm
    · change 0 = d 1
      exact h5.2.1.symm
    · change 1 = d 2
      exact h5.2.2.1.symm
    · change 1 = d 3
      exact h5.2.2.2.symm
  · refine ⟨6, ?_⟩
    ext a
    fin_cases a
    · change 0 = d 0
      exact h6.1.symm
    · change 0 = d 1
      exact h6.2.1.symm
    · change 2 = d 2
      exact h6.2.2.1.symm
    · change 0 = d 3
      exact h6.2.2.2.symm
  · refine ⟨7, ?_⟩
    ext a
    fin_cases a
    · change 0 = d 0
      exact h7.1.symm
    · change 1 = d 1
      exact h7.2.1.symm
    · change 0 = d 2
      exact h7.2.2.1.symm
    · change 1 = d 3
      exact h7.2.2.2.symm
  · refine ⟨8, ?_⟩
    ext a
    fin_cases a
    · change 0 = d 0
      exact h8.1.symm
    · change 1 = d 1
      exact h8.2.1.symm
    · change 1 = d 2
      exact h8.2.2.1.symm
    · change 0 = d 3
      exact h8.2.2.2.symm
  · refine ⟨9, ?_⟩
    ext a
    fin_cases a
    · change 0 = d 0
      exact h9.1.symm
    · change 2 = d 1
      exact h9.2.1.symm
    · change 0 = d 2
      exact h9.2.2.1.symm
    · change 0 = d 3
      exact h9.2.2.2.symm

variable {K : Type*} [CommRing K]
lemma homogeneous_expansion (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 2) :
    p = ∑ j : Fin 10, monomial (exponent j) (p.coeff (exponent j)) := by
  classical
  ext d
  simp only [coeff_sum, coeff_monomial]
  by_cases h : ∃ j, exponent j = d
  · obtain ⟨j,rfl⟩ := h
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [ite_eq_right (exponent_inj.ne hb)]
    · simp
  · have hd : d.degree ≠ 2 := fun hd => h (exponents_exhaust d hd)
    rw [hp.coeff_eq_zero hd]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (fun hh => h ⟨j,hh⟩)]

lemma coefficients_nonzero {p : MvPolynomial (Fin 4) K} (hp : p.IsHomogeneous 2) (hne : p ≠ 0) :
    (fun j => p.coeff (exponent j)) ≠ 0 := by
  intro hz
  apply hne
  rw [homogeneous_expansion p hp]
  apply Finset.sum_eq_zero
  intro j _
  have hh := congrFun hz j
  change p.coeff (exponent j) = 0 at hh
  rw [hh, monomial_zero]

lemma eval_expansion (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 2) (x : Fin 4 → K) :
    p.eval x = ∑ j : Fin 10, (∏ i : Fin 4, x i ^ powers j i) * p.coeff (exponent j) := by
  conv_lhs => rw [homogeneous_expansion p hp]
  simp only [eval_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [exponent_apply]
  ring
end QuadraticBasis

end

end OAI
