import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W24

open Polynomial Finset

noncomputable def powerPrefixPolynomial (d : ℕ) : Polynomial ℚ :=
  C ((d + 1 : ℚ)⁻¹) * (Polynomial.bernoulli (d + 1) - C (_root_.bernoulli (d + 1)))

theorem powerPrefixPolynomial_eval (d n : ℕ) :
    (powerPrefixPolynomial d).eval (n : ℚ) = ∑ j ∈ range n, (j : ℚ) ^ d := by
  rw [powerPrefixPolynomial, eval_mul, eval_C, eval_sub, eval_C]
  rw [← Polynomial.sum_range_pow_eq_bernoulli_sub n d]
  have hd : (d + 1 : ℚ) ≠ 0 := by positivity
  exact inv_mul_cancel_left₀ hd _

theorem powerPrefixPolynomial_degree_le (d : ℕ) :
    (powerPrefixPolynomial d).natDegree ≤ d + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj0 : j ≠ 0 := by omega
  simp only [powerPrefixPolynomial, coeff_C_mul, coeff_sub,
    Polynomial.coeff_bernoulli, ite_eq_right (by omega : ¬j ≤ d + 1),
    coeff_C, ite_eq_right hj0, sub_zero, mul_zero]

theorem powerPrefixPolynomial_top_coefficient (d : ℕ) :
    (powerPrefixPolynomial d).coeff (d + 1) = (d + 1 : ℚ)⁻¹ := by
  simp [powerPrefixPolynomial, coeff_C_mul, Polynomial.coeff_bernoulli]

noncomputable def polynomialPrefix (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ range (p.natDegree + 1), C (p.coeff i) * powerPrefixPolynomial i

theorem polynomialPrefix_eval (p : Polynomial ℚ) (n : ℕ) :
    (polynomialPrefix p).eval (n : ℚ) = ∑ j ∈ range n, p.eval (j : ℚ) := by
  simp only [polynomialPrefix, eval_finsetSum, eval_mul, eval_C,
    powerPrefixPolynomial_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Polynomial.eval_eq_sum_range (p := p) (j : ℚ)).symm

theorem polynomialPrefix_degree_le (p : Polynomial ℚ) :
    (polynomialPrefix p).natDegree ≤ p.natDegree + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans
    ((powerPrefixPolynomial_degree_le i).trans (by
      have hii := Finset.mem_range.mp hi
      omega))

theorem polynomialPrefix_top_coefficient (p : Polynomial ℚ) :
    (polynomialPrefix p).coeff (p.natDegree + 1) =
      p.leadingCoeff * (p.natDegree + 1 : ℚ)⁻¹ := by
  rw [polynomialPrefix, finsetSum_coeff]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [coeff_C_mul, powerPrefixPolynomial_top_coefficient, coeff_natDegree]
  · intro i hi hne
    have hz : (powerPrefixPolynomial i).coeff (p.natDegree + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((powerPrefixPolynomial_degree_le i).trans_lt (by
        have hii := Finset.mem_range.mp hi
        omega))
    rw [coeff_C_mul, hz, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

theorem polynomialPrefix_natDegree (p : Polynomial ℚ) (hp : p ≠ 0) :
    (polynomialPrefix p).natDegree = p.natDegree + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomialPrefix_degree_le p)
  rw [polynomialPrefix_top_coefficient]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (inv_ne_zero (by positivity))

theorem exists_eventual_cumulative_polynomial
    (values : ℕ → ℕ) (p : Polynomial ℚ) (hp0 : p ≠ 0) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ)) :
    ∃ q : Polynomial ℚ, q.natDegree = p.natDegree + 1 ∧
      ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) =
        ((∑ j ∈ range (n + 1), values j : ℕ) : ℚ) := by
  let c : ℚ := (∑ j ∈ range N, (values j : ℚ)) - (polynomialPrefix p).eval (N : ℚ)
  let q : Polynomial ℚ := (polynomialPrefix p).comp (X + C 1) + C c
  have hsum (m : ℕ) (hm : N ≤ m) :
      (polynomialPrefix p).eval (m : ℚ) + c = ∑ j ∈ range m, (values j : ℚ) := by
    induction m, hm using Nat.le_induction with
    | base => simp [c]
    | succ m hm ih =>
        rw [polynomialPrefix_eval, Finset.sum_range_succ,
          ← polynomialPrefix_eval, hp m hm, Finset.sum_range_succ]
        linarith
  refine ⟨q, ?_, ?_⟩
  · simp only [q, natDegree_add_C, natDegree_comp, natDegree_X, mul_one,
      polynomialPrefix_natDegree p hp0]
  · intro n hn
    simpa only [q, eval_add, eval_comp, eval_X, eval_C, Nat.cast_add, Nat.cast_one,
      Nat.cast_sum] using hsum (n + 1) (by omega)

end WeightedTorusJets.W24

end

end SiegelZeros

end OAI
