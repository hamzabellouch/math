import OAI.NumberTheory.JointDickman.Amplification.FirstRepresentationSum

namespace OAI

/-! # Exact fair-retention normalization of the latent candidate kernel -/

namespace JointDickman
open Finset

open Classical in
theorem candidateCoefficientFactor_retention {B L M : ℕ} {τ C : ℝ}
    (hB : 1 < B) (χ : BlockCandidateIndex M → ℝ) (i t : Fin M)
    {S R A D : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B)
    (hA : A ∈ endpointSplits B L τ C S) (hD : D ∈ endpointSplits B L τ C R) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D))*
      regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D) =
    (B : ℝ)*independentRootMean B L τ C*subsetRetentionMass S A*subsetRetentionMass R D*
      regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*χ ((i,t),(A,D)) := by
  obtain ⟨hAS,hAr,hAc⟩ := mem_endpointSplits.mp hA
  obtain ⟨hDR,hDr,hDc⟩ := mem_endpointSplits.mp hD
  have hleft := regular_arithmetic_split_identity (L := L) (τ := τ) (C := C) hB hS hAS
  have hright := regular_arithmetic_split_identity (L := L) (τ := τ) (C := C) hB hR hDR
  simp only [hAr,hAc,and_self,ite_true,mul_one] at hleft
  simp only [hDr,hDc,and_self,ite_true,mul_one] at hright
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  unfold candidateCoefficientFactor candidateLow candidateHigh
  calc
    _ = ((regularCoefficientWeight B L τ C (∏ p ∈ A,p)*
          regularResidueWeight B L τ C (S \ A))*
        (regularCoefficientWeight B L τ C (∏ p ∈ D,p)*
          regularResidueWeight B L τ C (R \ D))/(B : ℝ))*
        regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
        χ ((i,t),(A,D))*independentRootMean B L τ C := by ring
    _ = _ := by
      rw [hleft,hright]
      field_simp [hB0]

open Classical in
theorem candidateSiteKernel_retention_sum {B L T H M : ℕ} {τ C : ℝ}
    (hB : 1 < B) (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ endpointSplits B L τ C S, ∑ D ∈ endpointSplits B L τ C R,
          subsetRetentionMass S A*subsetRetentionMass R D*
            (if BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) then
              regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
                χ ((i,t),(A,D)) else 0) := by
  rw [candidateSiteKernel_factor_sum χ i t hit]
  unfold candidatePairRepresentations
  rw [sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  by_cases had : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · simp only [had,ite_true]
    rw [candidateCoefficientFactor_retention hB χ i t hS hR hA hD]
    ring
  · simp [had]


open Classical in
/-- The two regularity indicators are the only restrictions in the
arithmetic-to-fair normalization of an endpoint and its remainder. -/
theorem candidateCoefficientFactor_fair {B L M : ℕ} {τ C : ℝ}
    (hB : 1 < B) (χ : BlockCandidateIndex M → ℝ) (i t : Fin M)
    {S R A D : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B)
    (hAS : A ⊆ S) (hDR : D ⊆ R) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D))*
      regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D) =
    (B : ℝ)*independentRootMean B L τ C*subsetRetentionMass S A*subsetRetentionMass R D*
      (if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
          (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
        regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*χ ((i,t),(A,D))
      else 0) := by
  have hleft := regular_arithmetic_split_identity (L := L) (τ := τ) (C := C) hB hS hAS
  have hright := regular_arithmetic_split_identity (L := L) (τ := τ) (C := C) hB hR hDR
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  unfold candidateCoefficientFactor candidateLow candidateHigh
  calc
    _ = ((regularCoefficientWeight B L τ C (∏ p ∈ A,p)*
          regularResidueWeight B L τ C (S \ A))*
        (regularCoefficientWeight B L τ C (∏ p ∈ D,p)*
          regularResidueWeight B L τ C (R \ D))/(B : ℝ))*
        regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
        χ ((i,t),(A,D))*independentRootMean B L τ C := by ring
    _ = _ := by
      rw [hleft,hright]
      by_cases ha : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)
      all_goals by_cases hd : RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)
      all_goals simp only [ha,hd,and_self,and_false,false_and,ite_true,ite_false,
        mul_zero,zero_mul]
      all_goals field_simp [hB0] <;> ring

open Classical in
/-- Exact candidate kernel on the ambient prime powerset. This form keeps
all restrictions visible before estimating the discarded regularity events. -/
theorem candidateSiteKernel_fair_sum {B L T H M : ℕ} {τ C : ℝ}
    (hB : 1 < B) (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
          subsetRetentionMass S A*subsetRetentionMass R D*
            (if BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) ∧
                (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
                (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
              regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*χ ((i,t),(A,D))
            else 0) := by
  rw [candidateSiteKernel_unrestricted_sum χ i t hit S R hS hR,
    Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  by_cases hAS : A ⊆ S
  · by_cases hDR : D ⊆ R
    · by_cases had : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
      · rw [ite_eq_left ⟨had,hAS,hDR⟩,
          candidateCoefficientFactor_fair hB χ i t hS hR hAS hDR]
        simp only [had,true_and]
        ring
      · simp [had]
    · simp [hDR,subsetRetentionMass]
  · simp [hAS,subsetRetentionMass]

end JointDickman

end OAI
