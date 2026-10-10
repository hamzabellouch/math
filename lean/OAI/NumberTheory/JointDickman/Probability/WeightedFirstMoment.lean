import OAI.NumberTheory.JointDickman.Probability.ArithmeticMomentComparison
import OAI.NumberTheory.JointDickman.Probability.SitePairFirstLaw
import OAI.NumberTheory.JointDickman.Amplification.InteriorRegularity

namespace OAI

/-! # A positive first moment for weights equal to one on the interior rectangle -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem fairRegularAmplificationAt_nonneg (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    0 ≤ fairRegularAmplificationAt B L τ C A D := by
  unfold fairRegularAmplificationAt
  apply sum_nonneg
  intro R hR
  apply sum_nonneg
  intro Q hQ
  split_ifs
  · exact mul_nonneg
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hA (mem_powerset.mp hR))
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hD (mem_powerset.mp hQ))
  · exact le_rfl

open Classical in
theorem independentWeighted_first_identity (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    independentAmplificationMoment B L τ C w 1 = (B : ℝ) *
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        fairRegularAmplificationAt B L τ C A D * w (∏ p ∈ A, p) (∏ p ∈ D, p) := by
  let H := fun A R D Q => if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
    RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q then w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0
  have he := sitePair_first_law (auxiliaryPrimes B) H
  have he' : (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D => H A (S \ A) D (R \ D))) =
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        fairRegularAmplificationAt B L τ C A D * w (∏ p ∈ A, p) (∏ p ∈ D, p) := by
    rw [he]
    unfold fairRegularAmplificationAt
    simp only [sum_mul]
    apply sum_congr rfl
    intro A _
    apply sum_congr rfl
    intro D _
    apply sum_congr rfl
    intro R _
    apply sum_congr rfl
    intro Q _
    dsimp only [H]
    simp only [and_assoc]
    split_ifs <;> ring
  calc
    _ = (B : ℝ) * (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
        ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
          sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D => H A (S \ A) D (R \ D))) := by
      simp only [independentAmplificationMoment, pow_one, independentWeightedAmplification, mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      dsimp only [H]
      ac_rfl
    _ = _ := congrArg (fun x : ℝ => (B : ℝ)*x) he'

open Classical in
theorem interior_mass_le_weighted_first (B L T : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ a c, 0 ≤ w a c)
    (hi : ∀ a c, (a,c) ∈ amplificationInteriorPairs B T → 1 ≤ w a c) :
    (B : ℝ)*fairRegularInteriorMass B L T τ C ≤ independentAmplificationMoment B L τ C w 1 := by
  rw [independentWeighted_first_identity]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  have hn := fairRegularAmplificationAt_nonneg B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationInteriorPairs B T
  · rw [ite_eq_left hp]
    exact le_mul_of_one_le_right hn (hi _ _ hp)
  · rw [ite_eq_right hp]
    exact mul_nonneg hn (hw _ _)

theorem independentWeighted_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ) (w : ℕ → ℕ → ℝ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        (∀ a c, 0 ≤ w a c) → (∀ a c, (a,c) ∈ amplificationInteriorPairs B T → 1 ≤ w a c) →
        d ≤ independentAmplificationMoment B L τ C w 1 := by
  obtain ⟨d,hd,hl⟩ := interior_regular_first_lower hFord hSD hM hMP
  refine ⟨d,hd,?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hl L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hb] with B hB
  intro C T w hC hT hTsize hw hi
  exact (hB C T hC hT hTsize).trans (interior_mass_le_weighted_first B L T τ C w hw hi)

end JointDickman

end OAI
