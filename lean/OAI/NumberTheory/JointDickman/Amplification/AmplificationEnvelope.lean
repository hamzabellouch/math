import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitProduct
import OAI.NumberTheory.JointDickman.Probability.AmplificationSecondMoment

namespace OAI

/-! # The independent-model amplification envelope and its second moment -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def independentAmplificationEnvelope (B L T : ℕ) (τ C : ℝ)
    (S R : Finset ℕ) : ℝ :=
  B * sitePairSplitAverage (auxiliaryPrimes B) S R
    (fun A D => if amplificationSplitGood B L T τ C S R A D then 1 else 0)

open Classical in
theorem independentAmplificationEnvelope_second_identity (B L T : ℕ) (τ C : ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
    ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
      (independentAmplificationEnvelope B L T τ C S R)^2) =
    (B : ℝ)^2 * twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) := by
  let F := fun S R A D => if amplificationSplitGood B L T τ C S R A D then (1 : ℝ) else 0
  have hp : (∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
      F x.site₁.val x.site₂.val x.first₁.val x.first₂.val *
      F x.site₁.val x.site₂.val x.second₁.val x.second₂.val) =
      twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) := by
    apply sum_congr rfl
    intro x _
    unfold F bothAmplificationSplitsGood
    by_cases h₁ : amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.first₁.val x.first₂.val <;>
    by_cases h₂ : amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.second₁.val x.second₂.val <;>
      simp only [h₁, h₂, and_self, and_false, false_and, ite_true, ite_false, mul_one, mul_zero]
  rw [← hp, twoSiteSplit_product]
  simp only [independentAmplificationEnvelope, mul_sum]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro R _
  dsimp only [F]
  ring

/-- The B-normalized fair-split envelope has a bounded second moment. -/
theorem independentAmplificationEnvelope_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        (independentAmplificationEnvelope B L T τ C S R)^2) ≤ K := by
  intro L τ C
  obtain ⟨K, hK, hb⟩ := amplification_second_moment_probability hFord hM L τ C
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop 0] with B hB hB0
  intro T hT hTsize
  rw [independentAmplificationEnvelope_second_identity]
  have hz : (B : ℝ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hB0))
  calc
    _ ≤ (B : ℝ)^2 * (K / (B : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (hB T hT hTsize) (sq_nonneg _)
    _ = K := by field_simp

end JointDickman

end OAI
