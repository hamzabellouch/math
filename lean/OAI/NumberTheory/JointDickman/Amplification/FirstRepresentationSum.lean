import OAI.NumberTheory.JointDickman.Counting.CandidateCoefficientFactor

namespace OAI

/-! # Reindexing the kernel by a first coefficient pair -/

namespace JointDickman
open Finset Classical

/-- The unrestricted pair sum is exact: the coefficient and remainder
weights themselves impose the four endpoint regularity conditions. -/
theorem candidateSiteKernel_unrestricted_sum {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (S R : Finset ℕ) (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
        if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
          candidateCoefficientFactor B L τ C χ ((i,t),ab)*
            regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
        else 0 := by
  rw [candidateSiteKernel_factor_sum χ i t hit S R]
  let J := (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset
  have hsub : candidatePairRepresentations B L T H τ C i t S R ⊆ J := by
    intro ab hab
    obtain ⟨ha,hd⟩ := mem_product.mp (mem_filter.mp hab).1
    exact mem_product.mpr ⟨mem_powerset.mpr ((mem_endpointSplits.mp ha).1.trans hS),
      mem_powerset.mpr ((mem_endpointSplits.mp hd).1.trans hR)⟩
  let w := fun ab : Finset ℕ × Finset ℕ =>
    if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
      candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
    else 0
  calc
    _ = ∑ ab ∈ candidatePairRepresentations B L T H τ C i t S R, w ab := by
      apply sum_congr rfl
      intro ab hab
      obtain ⟨hp,he⟩ := mem_filter.mp hab
      obtain ⟨ha,hd⟩ := mem_product.mp hp
      exact (ite_eq_left ⟨he,(mem_endpointSplits.mp ha).1,(mem_endpointSplits.mp hd).1⟩).symm
    _ = ∑ ab ∈ J, w ab := by
      apply sum_subset hsub
      intro ab hab hnot
      dsimp only [w]
      split_ifs with hc
      · have hpair := mem_product.mp hab
        have hA := mem_powerset.mp hpair.1
        have hD := mem_powerset.mp hpair.2
        by_cases ha : RegularPrimeSet B L τ C ab.1
        · by_cases hd : RegularPrimeSet B L τ C ab.2
          · by_cases hs : RegularPrimeSet B L τ C (S \ ab.1)
            · by_cases hr : RegularPrimeSet B L τ C (R \ ab.2)
              · exact False.elim (hnot (mem_filter.mpr ⟨mem_product.mpr
                  ⟨mem_endpointSplits.mpr ⟨hc.2.1,ha,hs⟩,
                   mem_endpointSplits.mpr ⟨hc.2.2,hd,hr⟩⟩,hc.1⟩))
              · simp only [regularResidueWeight,hr,ite_false,mul_zero]
            · simp only [regularResidueWeight,hs,ite_false,mul_zero,zero_mul]
          · rw [candidateCoefficientFactor_zero_right χ i t hD hd]
            simp
        · rw [candidateCoefficientFactor_zero_left χ i t hA ha]
          simp
      · rfl

/-- Averaging after fixing the first pair produces exactly its tilted
remainder law. The test can be the actual representation count. -/
theorem candidateSiteKernel_weighted_expectation {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R*
        candidateSiteKernel B L T H M τ C χ i t S R) =
    ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
      if BlockCandidateAdmissible B L T H τ C ((i,t),ab) then
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        (remainderTiltNormalizer B ab.1/(∏ p ∈ ab.1, p : ℕ))*
        (remainderTiltNormalizer B ab.2/(∏ p ∈ ab.2, p : ℕ))*
        regularTiltAverage B L τ C ab.1 (fun U => regularTiltAverage B L τ C ab.2
          (fun V => F (ab.1 ∪ U) (ab.2 ∪ V))) else 0 := by
  let J := (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset
  let W := fun (ab : Finset ℕ × Finset ℕ) (S R : Finset ℕ) =>
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R*
      if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
      else 0
  have hexpand : (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R*
        candidateSiteKernel B L T H M τ C χ i t S R) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        ∑ ab ∈ J, W ab S R := by
    apply sum_congr rfl
    intro S hS
    apply sum_congr rfl
    intro R hR
    rw [candidateSiteKernel_unrestricted_sum χ i t hit S R (mem_powerset.mp hS) (mem_powerset.mp hR),mul_sum]
  rw [hexpand]
  calc
    _ = ∑ ab ∈ J, ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        W ab S R := by
      simp_rw [sum_comm (s := (auxiliaryPrimes B).powerset) (t := J)]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      have hp := mem_product.mp hab
      have hA := mem_powerset.mp hp.1
      have hD := mem_powerset.mp hp.2
      by_cases he : BlockCandidateAdmissible B L T H τ C ((i,t),ab)
      · rw [ite_eq_left he]
        have hpoint (S R : Finset ℕ) : W ab S R =
            candidateCoefficientFactor B L τ C χ ((i,t),ab)*
              (if ab.1 ⊆ S ∧ ab.2 ⊆ R then
                bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
                bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
                regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)*F S R
              else 0) := by
          dsimp only [W]
          simp only [he,true_and]
          split_ifs <;> ring
        simp_rw [hpoint,← mul_sum]
        rw [regular_pair_change_of_measure hA hD F]
        ring
      · simp only [W,he,false_and,ite_false,mul_zero,sum_const_zero]

end JointDickman

end OAI
