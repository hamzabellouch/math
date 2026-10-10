import OAI.NumberTheory.JointDickman.Amplification.AmplificationEnvelope
import OAI.NumberTheory.JointDickman.Probability.SitePairFirstLaw

namespace OAI

/-! # The positive first moment of the independent amplification envelope -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem independentAmplificationEnvelope_first_identity (B L T : ℕ) (τ C : ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
    ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
      independentAmplificationEnvelope B L T τ C S R) =
    (B : ℝ) * fairRegularAmplificationMass B L T τ C := by
  let H := fun A R D Q => if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T ∧
      RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q then (1 : ℝ) else 0
  have he : (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D => H A (S \ A) D (R \ D))) =
      fairRegularAmplificationMass B L T τ C := by
    rw [sitePair_first_law]
    unfold fairRegularAmplificationMass fairRegularAmplificationAt
    apply sum_congr rfl
    intro A _
    apply sum_congr rfl
    intro D _
    by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
    · simp only [hp, ite_true]
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro Q _
      dsimp only [H]
      simp only [hp, true_and, and_assoc]
      split_ifs <;> simp only [mul_one, mul_zero]
    · simp only [hp, ite_false, H, false_and, mul_zero, sum_const_zero]
  calc
    _ = (B : ℝ) * (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
        ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
          sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D => H A (S \ A) D (R \ D))) := by
      simp only [independentAmplificationEnvelope, mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      unfold amplificationSplitGood
      dsimp only [H]
      ac_rfl
    _ = _ := congrArg (fun x : ℝ => (B : ℝ) * x) he

/-- A positive first moment, uniformly after choosing the regularity cutoff. -/
theorem independentAmplificationEnvelope_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
        d ≤ ∑ S ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
          ∑ R ∈ (auxiliaryPrimes B).powerset,
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
            independentAmplificationEnvelope B L T τ C S R := by
  simp only [independentAmplificationEnvelope_first_identity]
  exact regular_amplification_first_moment_lower hFord hSD hM hMP

end JointDickman

end OAI
