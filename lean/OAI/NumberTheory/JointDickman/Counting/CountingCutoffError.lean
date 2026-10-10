import OAI.NumberTheory.JointDickman.Amplification.RampedCandidate
import OAI.NumberTheory.JointDickman.Counting.PeriodicCountingBand

namespace OAI

/-! # Exact error when the finite counting cutoff is replaced by its ramp -/
namespace JointDickman
open Finset

noncomputable def smoothCandidateCutoff {M : ℕ} (B T : ℕ) (e : BlockCandidateIndex M) : ℝ :=
  candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e

theorem smoothCandidateCutoff_nonneg {M : ℕ} (B T : ℕ) (e : BlockCandidateIndex M) :
    0 ≤ smoothCandidateCutoff B T e := by
  change 0 ≤ amplificationBump _*amplificationBump _*amplificationBump _
  exact mul_nonneg (mul_nonneg amplificationBump.nonneg amplificationBump.nonneg) amplificationBump.nonneg

open Classical in
theorem finiteCandidateCutoff_ramp_error {B T N u M : ℕ} {δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (e : BlockCandidateIndex M)
    (hc : 0 < candidateQuotient e) :
    |finiteCandidateCutoff B T N u e-
        rampedCandidateCutoff B T δ (((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))) e| ≤
      smoothCandidateCutoff B T e*
        (if ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1)) <
              (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e) ∧
            (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e) <
              ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))+δ then 1 else 0) := by
  rw [finiteCandidateCutoff_threshold hT e hc]
  let s := ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))
  let x := (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e)
  change |(if s < x then smoothCandidateCutoff B T e else 0)-
      smoothCandidateCutoff B T e*countingRamp δ s x| ≤ _
  have he : (if s < x then smoothCandidateCutoff B T e else 0)-
      smoothCandidateCutoff B T e*countingRamp δ s x =
      smoothCandidateCutoff B T e*((if s < x then 1 else 0)-countingRamp δ s x) := by
    split_ifs <;> ring
  rw [he,abs_mul,abs_of_nonneg (smoothCandidateCutoff_nonneg B T e)]
  rw [abs_of_nonneg (countingRamp_sharp_error hδ s x).1]
  exact mul_le_mul_of_nonneg_left (countingRamp_sharp_error hδ s x).2
    (smoothCandidateCutoff_nonneg B T e)

open Classical in
theorem candidateSiteKernel_cutoff_error {B L T H M : ℕ} {τ C : ℝ}
    (χ ψ ω : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ)
    (hω : ∀ A D, (A,D) ∈ candidatePairRepresentations B L T H τ C i t S R →
      |χ ((i,t),(A,D))-ψ ((i,t),(A,D))| ≤ ω ((i,t),(A,D))) :
    |candidateSiteKernel B L T H M τ C χ i t S R-
      candidateSiteKernel B L T H M τ C ψ i t S R| ≤
        candidateSiteKernel B L T H M τ C ω i t S R := by
  rw [candidateSiteKernel_factor_sum χ i t hit,candidateSiteKernel_factor_sum ψ i t hit,
    candidateSiteKernel_factor_sum ω i t hit,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro ab hab
  let w := candidateCoefficientFactor B L τ C (fun _ => 1) ((i,t),ab)*
    regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
  have hw : 0 ≤ w := mul_nonneg (mul_nonneg
    (candidateCoefficientFactor_nonneg B L τ C (fun _ => 1) ((i,t),ab) zero_le_one)
    (regularResidueWeight_nonneg ..)) (regularResidueWeight_nonneg ..)
  have hfactor (f : BlockCandidateIndex M → ℝ) :
      candidateCoefficientFactor B L τ C f ((i,t),ab)*
        regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2) =
      w*f ((i,t),ab) := by unfold w candidateCoefficientFactor; ring
  rw [hfactor,hfactor,hfactor,← mul_sub,abs_mul,abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (hω ab.1 ab.2 hab) hw

end JointDickman

end OAI
