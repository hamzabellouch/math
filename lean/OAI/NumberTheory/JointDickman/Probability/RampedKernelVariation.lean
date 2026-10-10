import OAI.NumberTheory.JointDickman.Counting.OriginRampShift
import OAI.NumberTheory.JointDickman.Probability.CutNormParameter

namespace OAI

/-! # Absolute-mass variation of the actual ramped candidate kernel -/
namespace JointDickman
open Finset Classical

theorem candidateMatrix_absoluteMass_sub {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v w : ι → ℝ) :
    kernelAbsoluteMass (fun i k => candidateMatrix row col v i k-candidateMatrix row col w i k) ≤
      (2*∑ e, |v e-w e|)/(Fintype.card κ : ℝ) := by
  unfold kernelAbsoluteMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp_rw [← candidateMatrix_sub]
  exact (sum_le_sum (fun i _ => sum_le_sum (fun k _ =>
    candidateMatrix_abs_le row col _ i k))).trans_eq (candidateMatrix_total row col _)

theorem rampedKernel_absolute_variation {B L T H M : ℕ} {τ C δ σ σ' : ℝ}
    (hδ : 0 < δ) (S : Fin M → Finset ℕ) :
    kernelAbsoluteMass (fun i k =>
      latentCandidateKernel B L T H M τ C S (rampedCandidateCutoff B T δ σ) i k-
      latentCandidateKernel B L T H M τ C S (rampedCandidateCutoff B T δ σ') i k) ≤
    (|σ-σ'|/δ)*kernelAbsoluteMass
      (latentCandidateKernel B L T H M τ C S (smoothCandidateCutoff B T)) := by
  let r := |σ-σ'|/δ
  have hw (e : BlockCandidateIndex M) :
      |candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ) e-
        candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ') e| ≤
      r*candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e := by
    rw [candidateMeanWeight_cutoff_error]
    have hf : |rampedCandidateCutoff B T δ σ e-rampedCandidateCutoff B T δ σ' e| ≤
        smoothCandidateCutoff B T e*r := by
      change |smoothCandidateCutoff B T e*countingRamp δ σ _-
        smoothCandidateCutoff B T e*countingRamp δ σ' _| ≤ _
      rw [← mul_sub,abs_mul,abs_of_nonneg (smoothCandidateCutoff_nonneg B T e)]
      exact mul_le_mul_of_nonneg_left (countingRamp_threshold_lipschitz hδ _ _ _)
        (smoothCandidateCutoff_nonneg B T e)
    exact (mul_le_mul_of_nonneg_left hf
      (candidateMeanWeight_nonneg B L τ C S (fun _ => 1) (fun _ => zero_le_one) e)).trans_eq (by
        rw [candidateMeanWeight_cutoff_factor B L τ C S (smoothCandidateCutoff B T) e]
        ring)
  calc
    _ ≤ (2*∑ e : blockCandidates B L T H M τ C S,
        |candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ) e.val-
          candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ') e.val|)/(M : ℝ) := by
      unfold latentCandidateKernel
      simpa only [Fintype.card_fin] using candidateMatrix_absoluteMass_sub
        (fun e : blockCandidates B L T H M τ C S => e.val.1.1) (fun e => e.val.1.2)
        (fun e => candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ) e.val)
        (fun e => candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ') e.val)
    _ ≤ (2*∑ e : blockCandidates B L T H M τ C S,
        r*candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e.val)/(M : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun e _ => hw e.val)) (by norm_num)
    _ = _ := by
      rw [latentCandidateKernel_absoluteMass S _ (smoothCandidateCutoff_nonneg B T),← mul_sum]
      ring

end JointDickman

end OAI
