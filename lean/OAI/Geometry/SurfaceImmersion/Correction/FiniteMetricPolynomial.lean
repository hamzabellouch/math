import Mathlib

namespace OAI

/-! Exact finite polynomial metric algebra for the periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def vectorPolynomialValue (n : ℕ) (a : ℕ → E) (z : ℝ) : E :=
  ∑ i ∈ Finset.range (n + 1), z ^ i • a i

def metricPolynomial (n : ℕ) (a b : ℕ → E) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial (i + j) (inner ℝ (a i) (b j))

lemma metricPolynomial_eval (n : ℕ) (a b : ℕ → E) (z : ℝ) :
    (metricPolynomial n a b).eval z =
      inner ℝ (vectorPolynomialValue n a z) (vectorPolynomialValue n b z) := by
  simp only [metricPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    vectorPolynomialValue, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- At each degree no larger than the vector degree, the usual convolution
contains every contributing term, with no truncation at either end. -/
lemma metricPolynomial_coeff {n r : ℕ} (hr : r ≤ n) (a b : ℕ → E) :
    (metricPolynomial n a b).coeff r =
      ∑ i ∈ Finset.range (r + 1), inner ℝ (a i) (b (r - i)) := by
  simp only [metricPolynomial, Polynomial.finsetSum_coeff]
  have hrow (i : ℕ) :
      (∑ j ∈ Finset.range (n + 1), (Polynomial.monomial (i + j) (inner ℝ (a i) (b j))).coeff r) =
        if i ≤ r then inner ℝ (a i) (b (r - i)) else 0 := by
    by_cases hi : i ≤ r
    · rw [ite_eq_left hi]
      have hc : (Polynomial.monomial (i + (r - i))
          (inner ℝ (a i) (b (r - i)))).coeff r = inner ℝ (a i) (b (r - i)) := by
        simp [Nat.add_sub_of_le hi]
      rw [← hc]
      apply Finset.sum_eq_single (r - i)
      · intro j hj hne
        rw [Polynomial.coeff_monomial]
        split_ifs with he
        · omega
        · rfl
      · intro hn
        exfalso
        apply hn
        exact Finset.mem_range.mpr (by omega)
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Polynomial.coeff_monomial]
      split_ifs with he
      · omega
      · rfl
  simp_rw [hrow]
  have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
  calc
    _ = ∑ i ∈ Finset.range (r + 1),
        if i ≤ r then inner ℝ (a i) (b (r - i)) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro i hin hir
      exact ite_eq_right (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hir)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma metricPolynomial_coeff_pos {n r : ℕ} (hr : r ≤ n) (hpos : 0 < r)
    (a b : ℕ → E) :
    (metricPolynomial n a b).coeff r = inner ℝ (a 0) (b r) + inner ℝ (a r) (b 0) +
      ∑ i ∈ Finset.Ico 1 r, inner ℝ (a i) (b (r - i)) := by
  rw [metricPolynomial_coeff hr, Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico (fun i => inner ℝ (a i) (b (r - i))) hpos]
  simp only [Finset.sum_range_one, Nat.sub_zero, Nat.sub_self]
  ring

lemma metricPolynomial_degree (n : ℕ) (a b : ℕ → E) :
    (metricPolynomial n a b).natDegree ≤ 2 * n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  simp only [metricPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hi hj
  rw [Polynomial.coeff_monomial]
  exact ite_eq_right (by omega)

/-- Split the exact metric polynomial at any chosen expansion order. -/
lemma metricPolynomial_expansion (n k : ℕ) (hk : k ≤ 2 * n + 1)
    (a b : ℕ → E) (z : ℝ) :
    inner ℝ (vectorPolynomialValue n a z) (vectorPolynomialValue n b z) =
      (∑ i ∈ Finset.range k, (metricPolynomial n a b).coeff i * z ^ i) +
      ∑ i ∈ Finset.Ico k (2 * n + 1), (metricPolynomial n a b).coeff i * z ^ i := by
  rw [← metricPolynomial_eval]
  conv_lhs => rw [(metricPolynomial n a b).as_sum_range' (2 * n + 1)
    (by have h := metricPolynomial_degree n a b; omega)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact (Finset.sum_range_add_sum_Ico _ hk).symm

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
