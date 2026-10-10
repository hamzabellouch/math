import OAI.NumberTheory.JointDickman.Amplification.FirstPairMassBound

namespace OAI

/-! # Using the tilted multiplicity estimate after fixing a first pair -/

namespace JointDickman
open Finset Classical

noncomputable def candidateMultiplicityMoment (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
    (candidatePairRepresentations B L T H τ C i t S R).card*
    candidateSiteKernel B L T H M τ C χ i t S R

/-- This is the exact point at which the previously proved tilted count
enters the square estimate. No regularity probability is divided out. -/
theorem candidateMultiplicityMoment_le_firstMass {B L T H M : ℕ} {τ C Q : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (hχ : ∀ e, 0 ≤ χ e)
    (i t : Fin M) (hit : i < t)
    (hcount : ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
      BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      tiltedCandidatePairCount B L T H τ C i t A D ≤ Q) :
    candidateMultiplicityMoment B L T H τ C χ i t ≤
      Q*candidateFirstPairMass B L T H τ C χ i t := by
  unfold candidateMultiplicityMoment
  rw [candidateSiteKernel_weighted_expectation χ i t hit]
  unfold candidateFirstPairMass
  rw [mul_sum]
  apply sum_le_sum
  intro ab hab
  have hp := mem_product.mp hab
  by_cases he : BlockCandidateAdmissible B L T H τ C ((i,t),ab)
  · simp only [he,ite_true]
    by_cases ha : RegularPrimeSet B L τ C ab.1
    · by_cases hd : RegularPrimeSet B L τ C ab.2
      · have hc := hcount ab.1 hp.1 ab.2 hp.2 he ha hd
        have hweight : 0 ≤ candidateCoefficientFactor B L τ C χ ((i,t),ab)*
            (remainderTiltNormalizer B ab.1/(∏ p ∈ ab.1, p : ℕ))*
            (remainderTiltNormalizer B ab.2/(∏ p ∈ ab.2, p : ℕ)) :=
          mul_nonneg (mul_nonneg (candidateCoefficientFactor_nonneg _ _ _ _ _ _ (hχ _))
            (div_nonneg (remainderTiltNormalizer_nonneg _ _) (Nat.cast_nonneg _)))
            (div_nonneg (remainderTiltNormalizer_nonneg _ _) (Nat.cast_nonneg _))
        exact (mul_le_mul_of_nonneg_left hc hweight).trans_eq (mul_comm _ _)
      · rw [candidateCoefficientFactor_zero_right χ i t (mem_powerset.mp hp.2) hd]
        simp
    · rw [candidateCoefficientFactor_zero_left χ i t (mem_powerset.mp hp.1) ha]
      simp
  · simp only [he,ite_false,mul_zero,le_refl]

end JointDickman

end OAI
