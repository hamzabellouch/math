import OAI.NumberTheory.JointDickman.Amplification.AmplificationPointBounds

namespace OAI

/-! # Bounded coefficient cutoffs in the independent amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def independentWeightedAmplification (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (S R : Finset ℕ) : ℝ :=
  B * sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D =>
    if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
    then w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0)

open Classical in
theorem independentWeightedAmplification_nonneg (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c) (S R : Finset ℕ) :
    0 ≤ independentWeightedAmplification B L τ C w S R := by
  unfold independentWeightedAmplification sitePairSplitAverage
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sum_nonneg
  intro A _
  apply sum_nonneg
  intro D _
  apply mul_nonneg (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))
  dsimp only
  split_ifs
  · exact hw _ _
  · exact le_rfl

open Classical in
theorem independentWeightedAmplification_le_envelope (B L T : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, w a c ≤ 1)
    (hsupp : ∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0)
    (S R : Finset ℕ) :
    independentWeightedAmplification B L τ C w S R ≤ independentAmplificationEnvelope B L T τ C S R := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  apply sitePairSplitAverage_mono
  intro A _ D _
  unfold amplificationSplitGood
  by_cases hr : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  · by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
    · simp only [hr, hp, true_and, ite_true]
      exact hw _ _
    · simp only [hr, hp, false_and, and_self, ite_true, ite_false, hsupp _ _ hp, le_refl]
  · simp only [hr, and_false, ite_false, le_refl]

theorem weightedAmplification_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (T : ℕ) (w : ℕ → ℕ → ℝ), 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
      (∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0) →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        (independentWeightedAmplification B L τ C w S R)^2) ≤ K := by
  intro L τ C
  obtain ⟨K, hK, hb⟩ := independentAmplificationEnvelope_second_bound hFord hM L τ C
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb] with B hB
  intro T w hT hTsize hw hsupp
  apply le_trans _ (hB T hT hTsize)
  apply sum_le_sum
  intro S hS
  have hnonneg (A : Finset ℕ) (hA : A ⊆ auxiliaryPrimes B) :
      0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) A := by
    apply bernoulliSubsetMass_nonneg hA
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).pos
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  apply mul_le_mul_of_nonneg_left _ (hnonneg S (mem_powerset.mp hS))
  apply sum_le_sum
  intro R hR
  apply mul_le_mul_of_nonneg_left _ (hnonneg R (mem_powerset.mp hR))
  have hx := independentWeightedAmplification_nonneg B L τ C w (fun a c => (hw a c).1) S R
  have hy := independentAmplificationEnvelope_nonneg B L T τ C S R
  exact (sq_le_sq₀ hx hy).mpr
    (independentWeightedAmplification_le_envelope B L T τ C w (fun a c => (hw a c).2) hsupp S R)

end JointDickman

end OAI
