import OAI.NumberTheory.JointDickman.Amplification.WeightedCandidateMultiplicity

namespace OAI

/-! # The integrated square of an actual latent edge -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def candidateSquareMoment (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
      (candidateSiteKernel B L T H M τ C χ i t S R)^2

theorem independentSubsetMass_nonneg {B : ℕ} {S : Finset ℕ}
    (hS : S ∈ (auxiliaryPrimes B).powerset) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S :=
  independentPrimeSetMass_nonneg B ⟨S,hS⟩

theorem candidateSquareMoment_le_multiplicity
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ (i t : Fin M), i < t →
        candidateSquareMoment B L T H τ C χ i t ≤
          (B : ℝ)^(-(22/100 : ℝ))*candidateMultiplicityMoment B L T H τ C χ i t := by
  filter_upwards [latentCandidateKernel_square_multiplicity hM hL hτ hτsmall] with B hB
  intro T H M C χ hχ i t hit
  have hpoint (S R : Finset ℕ) : (candidateSiteKernel B L T H M τ C χ i t S R)^2 ≤
      (B : ℝ)^(-(22/100 : ℝ))*(candidatePairRepresentations B L T H τ C i t S R).card*
        candidateSiteKernel B L T H M τ C χ i t S R := by
    have hh := hB C T H M (Function.update (fun _ => S) t R) χ hχ i t hit
    change (candidateSiteKernel B L T H M τ C χ i t S R)^2 ≤
      (B : ℝ)^(-(22/100 : ℝ))*
      (candidatePairRepresentations B L T H τ C i t
        ((Function.update (fun _ => S) t R) i) ((Function.update (fun _ => S) t R) t)).card*
      candidateSiteKernel B L T H M τ C χ i t S R at hh
    simpa only [Function.update_of_ne (ne_of_lt hit),Function.update_self] using hh
  unfold candidateSquareMoment candidateMultiplicityMoment
  rw [mul_sum]
  apply sum_le_sum
  intro S hS
  rw [mul_sum]
  apply sum_le_sum
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hpoint S R)
    (mul_nonneg (independentSubsetMass_nonneg hS) (independentSubsetMass_nonneg hR))
  convert hh using 1; ring

end JointDickman

end OAI
