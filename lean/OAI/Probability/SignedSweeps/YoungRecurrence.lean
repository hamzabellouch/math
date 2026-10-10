import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Polynomial

def youngRecurrencePolynomial {I : Type*} (s : Finset I) (x : I → ℝ) : ℝ[X] :=
  X * ((∏ i ∈ s, (X - C (x i + 1))) - ∏ i ∈ s, (X - C (x i))) +
    C (s.card : ℝ) * ∏ i ∈ s, (X - C (x i))

lemma youngRecurrencePolynomial_empty {I : Type*} (x : I → ℝ) :
    youngRecurrencePolynomial ∅ x = 0 := by simp [youngRecurrencePolynomial]

lemma youngRecurrencePolynomial_insert {I : Type*} (s : Finset I) (x : I → ℝ)
    (a : I) (ha : a ∉ s) :
    youngRecurrencePolynomial (insert a s) x =
      (X - C (x a + 1)) * youngRecurrencePolynomial s x +
        C ((s.card : ℝ) - x a) * ∏ i ∈ s, (X - C (x i)) := by
  simp only [youngRecurrencePolynomial, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
    Nat.cast_add, Nat.cast_one, map_add, map_sub, map_one]
  ring

lemma youngRecurrencePolynomial_coefficients {I : Type*} (s : Finset I) (x : I → ℝ) :
    (∀ k, s.card ≤ k → (youngRecurrencePolynomial s x).coeff k = 0) ∧
    (youngRecurrencePolynomial s x).coeff (s.card - 1) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) / 2 - ∑ i ∈ s, x i := by
  induction s using Finset.induction_on with
  | empty => simp [youngRecurrencePolynomial]
  | @insert a s ha ih =>
    rw [youngRecurrencePolynomial_insert s x a ha]
    have hp : (∏ i ∈ s, (X - C (x i))).coeff s.card = (1 : ℝ) := by
      rw [← natDegree_finsetProd_X_sub_C_eq_card s x]
      exact (monic_prod_X_sub_C x s).leadingCoeff
    have hp0 (k : ℕ) (hk : s.card < k) :
        (∏ i ∈ s, (X - C (x i))).coeff k = (0 : ℝ) := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa using hk
    simp only [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, Nat.cast_add, Nat.cast_one]
    constructor
    · intro k hk
      have hn : 0 < k := by omega
      rw [coeff_add, sub_mul, coeff_sub, coeff_C_mul, coeff_C_mul]
      rw [show k = k - 1 + 1 by omega, coeff_X_mul]
      rw [ih.1 (k - 1) (by omega), ih.1 (k - 1 + 1) (by omega), hp0 (k - 1 + 1) (by omega)]
      ring
    · by_cases hs : s.card = 0
      · have he : s = ∅ := Finset.card_eq_zero.mp hs
        subst s
        simp [youngRecurrencePolynomial]
      · rw [Nat.add_sub_cancel, coeff_add, sub_mul, coeff_sub, coeff_C_mul, coeff_C_mul,
          ih.1 s.card le_rfl, hp]
        have hcoef : (X * youngRecurrencePolynomial s x).coeff s.card =
            (youngRecurrencePolynomial s x).coeff (s.card - 1) := by
          nth_rw 1 [show s.card = s.card - 1 + 1 by omega]
          rw [coeff_X_mul]
        rw [hcoef, ih.2]
        ring

lemma youngRecurrencePolynomial_degree {I : Type*} (s : Finset I) (x : I → ℝ) :
    (youngRecurrencePolynomial s x).degree < s.card := by
  rw [degree_lt_iff_coeff_zero]
  exact (youngRecurrencePolynomial_coefficients s x).1

theorem young_rational_recurrence {I : Type*} [DecidableEq I] (s : Finset I) (x : I → ℝ)
    (hx : Set.InjOn x s) :
    ∑ i ∈ s, x i * ∏ j ∈ s.erase i, ((x i - x j - 1) / (x i - x j)) =
      ∑ i ∈ s, x i - (s.card : ℝ) * ((s.card : ℝ) - 1) / 2 := by
  have hc := Lagrange.coeff_eq_sum hx (youngRecurrencePolynomial_degree s x)
  rw [(youngRecurrencePolynomial_coefficients s x).2] at hc
  have he (i : I) (hi : i ∈ s) :
      (youngRecurrencePolynomial s x).eval (x i) =
        -x i * ∏ j ∈ s.erase i, (x i - x j - 1) := by
    have hz : ∏ j ∈ s, (x i - x j) = 0 := Finset.prod_eq_zero hi (sub_self _)
    simp only [youngRecurrencePolynomial, eval_add, eval_mul, eval_X, eval_sub, eval_prod,
      eval_C, hz, sub_zero, mul_zero, add_zero]
    rw [← Finset.mul_prod_erase s _ hi]
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
    ring
  have ht (i : I) (hi : i ∈ s) :
      (youngRecurrencePolynomial s x).eval (x i) / ∏ j ∈ s.erase i, (x i - x j) =
        -(x i * ∏ j ∈ s.erase i, ((x i - x j - 1) / (x i - x j))) := by
    rw [he i hi, Finset.prod_div_distrib]
    ring
  rw [Finset.sum_congr rfl ht, Finset.sum_neg_distrib] at hc
  linarith

end SignedSweeps
end

end OAI
