import OAI.NumberTheory.JointDickman.Amplification.AmplificationRegularity
import OAI.NumberTheory.JointDickman.Probability.AmplificationFirstMoment

namespace OAI

/-! # A positive first moment after all four regularity cutoffs -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def fairRegularAmplificationAt (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ) : ℝ :=
  ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
    if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D) ∧
        (RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q) then
      fairSelectedRemainingMass (auxiliaryPrimes B) A R *
        fairSelectedRemainingMass (auxiliaryPrimes B) D Q else 0

open Classical in
noncomputable def fairRegularAmplificationMass (B L T : ℕ) (τ C : ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
      fairRegularAmplificationAt B L τ C A D else 0

theorem fairRegularAmplificationAt_complement (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    fairRegularAmplificationAt B L τ C A D + fairFourSubsetFailureAt B L τ C A D =
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D := by
  unfold fairRegularAmplificationAt fairFourSubsetFailureAt
  rw [← sum_add_distrib]
  calc
    _ = ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
        fairSelectedRemainingMass (auxiliaryPrimes B) A R *
          fairSelectedRemainingMass (auxiliaryPrimes B) D Q := by
      apply sum_congr rfl
      intro R _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro Q _
      split_ifs <;> simp only [zero_add, add_zero]
    _ = _ := by
      rw [← sum_mul_sum, fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hA,
        fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hD]

theorem fairRegularAmplificationMass_complement (B L T : ℕ) (τ C : ℝ) :
    fairRegularAmplificationMass B L T τ C + fairFourSubsetFailure B L T τ C =
      ∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
  rw [primeProductPair_sum_event]
  unfold fairRegularAmplificationMass fairFourSubsetFailure
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro A hA
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro D hD
  split_ifs
  · exact fairRegularAmplificationAt_complement B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  · exact add_zero 0

/-- The first moment remains bounded below after choosing the tail cutoff
sufficiently large, uniformly in every larger cutoff. -/
theorem regular_amplification_first_moment_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
        d ≤ (B : ℝ) * fairRegularAmplificationMass B L T τ C := by
  obtain ⟨d, hd, hpositive⟩ := amplification_first_moment_lower hSD hM hMP
  obtain ⟨K, hK, hloss⟩ := amplification_regularity_loss hFord hM
  refine ⟨d / 2, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, _, hε, hlarge⟩ := hloss L τ hL hτ
  let C₀ := max 0 (10 * Real.log (4 * K / d))
  have hC₀ : 0 ≤ C₀ := le_max_left _ _
  have htail : ∀ C : ℝ, C₀ ≤ C → K * Real.exp (-(1 / 10 : ℝ) * C) ≤ d / 4 := by
    intro C hC
    have hlog : 10 * Real.log (4 * K / d) ≤ C := (le_max_right _ _).trans hC
    have harg : -(1 / 10 : ℝ) * C ≤ -Real.log (4 * K / d) := by linarith only [hlog]
    calc
      _ ≤ K * Real.exp (-Real.log (4 * K / d)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hK.le
      _ = d / 4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 4 * K / d)]
        field_simp
  refine ⟨C₀, hC₀, ?_⟩
  have hsmall := hε.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d / (4 * K)))
  filter_upwards [hpositive, hlarge, hsmall] with B hp hl he
  intro C T hC hT hTsize
  have hpos := hp T hT hTsize
  have hlos := hl C T (hC₀.trans hC) hT hTsize
  have htails := htail C hC
  have heps : K * ε B ≤ d / 4 := by
    have hh := mul_le_mul_of_nonneg_left he hK.le
    have heq : K * (d / (4 * K)) = d / 4 := by field_simp
    rwa [heq] at hh
  have hc := congrArg (fun x : ℝ => (B : ℝ) * x) (fairRegularAmplificationMass_complement B L T τ C)
  rw [mul_add] at hc
  nlinarith only [hpos, hlos, htails, heps, hc]

end JointDickman

end OAI
