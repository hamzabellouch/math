import OAI.NumberTheory.TwoPoint.Bounds.PaddingSelectionLaw

namespace OAI

/-! The local three-boolean experiment agrees with first choosing all
available primes and then independently choosing two padding divisors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingAvailableLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Bool) :=
  FiniteLaw.independent (fun p : Q => paddingAvailabilityLaw p (hQ p p.property))

noncomputable def paddingDivisorLaw (Q : Finset ℕ) (a : Q → Bool) :
    FiniteLaw (Q → Bool) := FiniteLaw.independent (fun p => paddingSelectionLaw (a p))

noncomputable def paddingLog (Q : Finset ℕ) (b : Q → Bool) : ℝ :=
  ∑ p : Q, if b p then Real.log p else 0

def paddingTripleEquiv (Q : Finset ℕ) :
    (Q → Bool × (Bool × Bool)) ≃ ((Q → Bool) × ((Q → Bool) × (Q → Bool))) where
  toFun x := (fun p => (x p).1, fun p => (x p).2.1, fun p => (x p).2.2)
  invFun y p := (y.1 p, y.2.1 p, y.2.2 p)
  left_inv x := by funext p; rfl
  right_inv y := by rfl

lemma paddingPairLaw_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (a b c : Q → Bool) :
    (paddingPairLaw Q hQ).weight (fun p => (a p, b p, c p)) =
      (paddingAvailableLaw Q hQ).weight a *
        (paddingDivisorLaw Q a).weight b * (paddingDivisorLaw Q a).weight c := by
  simp only [paddingPairLaw, paddingPairLocal, paddingAvailableLaw, paddingDivisorLaw,
    FiniteLaw.independent, FiniteLaw.dependentProduct, FiniteLaw.product]
  rw [prod_mul_distrib, prod_mul_distrib]
  ring

lemma paddingPairLaw_average_nested (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : (Q → Bool) → (Q → Bool) → (Q → Bool) → ℝ) :
    (paddingPairLaw Q hQ).average
        (fun x => F (fun p => (x p).1) (fun p => (x p).2.1) (fun p => (x p).2.2)) =
      (paddingAvailableLaw Q hQ).average (fun a =>
        (paddingDivisorLaw Q a).average (fun b =>
          (paddingDivisorLaw Q a).average (fun c => F a b c))) := by
  calc
    _ = ∑ y : (Q → Bool) × ((Q → Bool) × (Q → Bool)),
        (paddingPairLaw Q hQ).weight (fun p => (y.1 p, y.2.1 p, y.2.2 p)) *
          F y.1 y.2.1 y.2.2 := by
      exact ((paddingTripleEquiv Q).symm.sum_comp
        (fun x => (paddingPairLaw Q hQ).weight x *
          F (fun p => (x p).1) (fun p => (x p).2.1) (fun p => (x p).2.2))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, paddingPairLaw_weight, FiniteLaw.average, mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro c _
      ring

lemma paddingPairDifference_value (Q : Finset ℕ) (x : Q → Bool × (Bool × Bool)) :
    paddingDifferenceValue Q (fun p => paddingPairDifference (x p)) =
      paddingLog Q (fun p => (x p).2.1) - paddingLog Q (fun p => (x p).2.2) := by
  unfold paddingDifferenceValue paddingLog
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  cases hb : (x p).2.1 <;> cases hc : (x p).2.2 <;>
    simp [paddingPairDifference, paddingDifferenceStep, hb, hc]

/-- Exact law of the difference of two conditionally sampled padding divisors. -/
theorem padding_pair_difference_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : ℝ → ℝ) :
    (paddingAvailableLaw Q hQ).average (fun a =>
      (paddingDivisorLaw Q a).average (fun b =>
        (paddingDivisorLaw Q a).average (fun c => F (paddingLog Q b - paddingLog Q c)))) =
      (paddingDifferenceLaw Q hQ).average (fun x => F (paddingDifferenceValue Q x)) := by
  rw [← paddingPairLaw_average_nested]
  simpa only [paddingPairDifference_value] using
    paddingPairLaw_average Q hQ (fun x => F (paddingDifferenceValue Q x))

end TwoPointCorrelations

end OAI
