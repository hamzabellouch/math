import OAI.NumberTheory.JointDickman.Amplification.LatentRowSquareBound
import OAI.NumberTheory.JointDickman.Amplification.CandidateExpectedDegree

namespace OAI

/-! # The integrated row estimate in the finite sampling notation -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem independentPrimePair_expectation (B : ℕ) (F : Finset ℕ → Finset ℕ → ℝ) :
    finiteExpectation (independentPrimeSetMass B) (fun S =>
      finiteExpectation (independentPrimeSetMass B) (fun R => F S.val R.val)) =
    ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R := by
  unfold finiteExpectation independentPrimeSetMass
  calc
    _ = ∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          ∑ R : (auxiliaryPrimes B).powerset,
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R.val*F S R.val :=
      sum_coe_sort _ _
    _ = _ := by
      apply sum_congr rfl
      intro S _
      rw [sum_coe_sort (auxiliaryPrimes B).powerset
        (fun R => bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R),mul_sum]
      apply sum_congr rfl
      intro R _
      ring

theorem latentPrimeSiteKernel_row_square_eq (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    siteRowSquareMass (fun _ : Fin M => independentPrimeSetMass B)
      (latentPrimeSiteKernel B L T H M τ C χ) i =
      ∑ t : Fin M, candidateSquareMoment B L T H τ C χ i t := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i,candidateSquareMoment_diag,zero_add]
  unfold siteRowSquareMass
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro t _
  exact independentPrimePair_expectation B
    (fun S R => (candidateSiteKernel B L T H M τ C χ i t S R)^2)

/-- The actual latent kernel satisfies the integrated square-mass premise
used by the finite sampling theorem, with the manuscript exponent. -/
theorem latentPrimeSiteKernel_row_square_mass
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        T ≤ auxiliaryCutoff B → (T : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ H →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ i : Fin M,
          siteRowSquareMass (fun _ : Fin M => independentPrimeSetMass B)
            (latentPrimeSiteKernel B L T H M τ C χ) i ≤ K*(B : ℝ)^(-(21/100 : ℝ)) := by
  obtain ⟨τ,K,hτ,hτcap,hτsampling,hK,hbound⟩ := candidateSquareMoment_row_bound hFord hM hL hη hcap
  refine ⟨τ,K,hτ,hτcap,hτsampling,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T H M C hT hTs hcut hT2 hH χ hχ i
  rw [latentPrimeSiteKernel_row_square_eq]
  exact hB T H M C hT hTs hcut hT2 hH χ hχ i

end JointDickman

end OAI
