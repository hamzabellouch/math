import OAI.NumberTheory.JointDickman.Counting.CountingShift

namespace OAI

/-! # From the exact endpoint cutoff to the common block-scale ramp -/
namespace JointDickman
open Finset

noncomputable def endpointRampedCutoff {M : ℕ} (B T N u : ℕ) (δ : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  rampedCandidateCutoff B T δ (((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))) e

open Classical in
noncomputable def endpointBandCutoff {M : ℕ} (B T N u : ℕ) (δ : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  smoothCandidateCutoff B T e*
    (if ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1)) <
          (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e) ∧
        (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e) <
          ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1))+δ then 1 else 0)

open Classical in
theorem candidateSiteKernel_const_mul {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (r : ℝ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    candidateSiteKernel B L T H M τ C (fun e => r*χ e) i t S R =
      r*candidateSiteKernel B L T H M τ C χ i t S R := by
  rw [candidateSiteKernel_factor_sum _ i t hit,candidateSiteKernel_factor_sum χ i t hit,mul_sum]
  apply sum_congr rfl
  intro ab _
  unfold candidateCoefficientFactor
  ring

open Classical in
theorem finite_endpoint_ramp_kernel_error {B L T H M N u : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    |candidateSiteKernel B L T H M τ C (finiteCandidateCutoff B T N u) i t S R-
      candidateSiteKernel B L T H M τ C (endpointRampedCutoff B T N u δ) i t S R| ≤
        candidateSiteKernel B L T H M τ C (endpointBandCutoff B T N u δ) i t S R := by
  apply candidateSiteKernel_cutoff_error _ _ _ i t hit S R
  intro A D hAD
  have ha := (mem_filter.mp hAD).2
  exact finiteCandidateCutoff_ramp_error hT hδ ((i,t),(A,D)) ha.2.2.2.1

open Classical in
theorem endpoint_origin_ramp_kernel_error {B L T H M N u : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    |candidateSiteKernel B L T H M τ C (endpointRampedCutoff B T N u δ) i t S R-
      candidateSiteKernel B L T H M τ C
        (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i t S R| ≤
      ((M : ℝ)/((T : ℝ)*(N+1)*δ))*
        candidateSiteKernel B L T H M τ C (smoothCandidateCutoff B T) i t S R := by
  rw [← candidateSiteKernel_const_mul _ _ i t hit]
  apply candidateSiteKernel_cutoff_error _ _ _ i t hit S R
  intro A D _
  change |smoothCandidateCutoff B T ((i,t),(A,D))*_-
    smoothCandidateCutoff B T ((i,t),(A,D))*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (smoothCandidateCutoff_nonneg B T ((i,t),(A,D)))]
  exact (mul_le_mul_of_nonneg_left
    (countingRamp_block_shift hδ hT N u i
      ((candidateLow ((i,t),(A,D)) : ℝ)/(T*candidateQuotient ((i,t),(A,D)))))
    (smoothCandidateCutoff_nonneg B T ((i,t),(A,D)))).trans_eq (mul_comm _ _)

open Classical in
theorem finite_origin_ramp_kernel_error {B L T H M N u : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    |candidateSiteKernel B L T H M τ C (finiteCandidateCutoff B T N u) i t S R-
      candidateSiteKernel B L T H M τ C
        (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i t S R| ≤
      candidateSiteKernel B L T H M τ C (endpointBandCutoff B T N u δ) i t S R+
      ((M : ℝ)/((T : ℝ)*(N+1)*δ))*
        candidateSiteKernel B L T H M τ C (smoothCandidateCutoff B T) i t S R :=
  (abs_sub_le _ (candidateSiteKernel B L T H M τ C (endpointRampedCutoff B T N u δ) i t S R) _).trans
    (add_le_add (finite_endpoint_ramp_kernel_error hT hδ i t hit S R)
      (endpoint_origin_ramp_kernel_error hT hδ i t hit S R))

end JointDickman

end OAI
