import OAI.NumberTheory.JointDickman.Counting.PeriodicCandidateCutoff
import OAI.NumberTheory.JointDickman.Amplification.CandidateCutoffNorm

namespace OAI

/-! # The finite-cutoff error in each retained candidate weight -/
namespace JointDickman
open Finset

 theorem candidateMeanWeight_cutoff_factor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      candidateMeanWeight B L τ C S (fun _ => 1) e*χ e := by
  rw [candidateMeanWeight_eq,candidateMeanWeight_eq]
  ring

theorem candidateMeanWeight_cutoff_error {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ ψ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    |candidateMeanWeight B L τ C S χ e-candidateMeanWeight B L τ C S ψ e| =
      candidateMeanWeight B L τ C S (fun _ => 1) e*|χ e-ψ e| := by
  rw [candidateMeanWeight_cutoff_factor B L τ C S χ e,
    candidateMeanWeight_cutoff_factor B L τ C S ψ e,← mul_sub,abs_mul,
    abs_of_nonneg (candidateMeanWeight_nonneg B L τ C S (fun _ => 1) (fun _ => zero_le_one) e)]

open Classical in
theorem finite_endpoint_weight_error {B L T H M N u : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (e : BlockCandidateIndex M)
    (he : e ∈ blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    |candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
        (finiteCandidateCutoff B T N u) e-
      candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
        (endpointRampedCutoff B T N u δ) e| =
    baseCandidateContribution B L T H M τ C e u*
      |(if ((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)) <
          (candidateLow e : ℝ)/(T*candidateQuotient e) then 1 else 0)-
        countingRamp δ (((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)))
          ((candidateLow e : ℝ)/(T*candidateQuotient e))| := by
  have hc := (mem_blockCandidates.mp he).2.2.2.2.1
  rw [candidateMeanWeight_cutoff_error,baseCandidateContribution,ite_eq_left he,
    candidateMeanWeight_cutoff_factor B L τ C _ (smoothCandidateCutoff B T) e,
    finiteCandidateCutoff_threshold hT e hc]
  unfold endpointRampedCutoff rampedCandidateCutoff
  let s := (((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1)))
  let x := (candidateLow e : ℝ)/(T*candidateQuotient e)
  have hs : s = ((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)) := by dsimp [s]; push_cast; rfl
  have hd : (if s < x then smoothCandidateCutoff B T e else 0)-
      smoothCandidateCutoff B T e*countingRamp δ s x =
      smoothCandidateCutoff B T e*((if s < x then 1 else 0)-countingRamp δ s x) := by
    split_ifs <;> ring
  change _*|(if s < x then smoothCandidateCutoff B T e else 0)-
    smoothCandidateCutoff B T e*countingRamp δ s x| = _
  rw [hd,abs_mul,abs_of_nonneg (smoothCandidateCutoff_nonneg B T e),hs]
  ring

end JointDickman

end OAI
