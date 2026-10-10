import OAI.NumberTheory.JointDickman.Amplification.BaseCandidateMassBound

namespace OAI

/-! # The within-block shift of the counting ramp disappears in the long average -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_absoluteMass {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (hχ : ∀ e, 0 ≤ χ e) :
    kernelAbsoluteMass (latentCandidateKernel B L T H M τ C S χ) =
      (2*∑ e : blockCandidates B L T H M τ C S,
        candidateMeanWeight B L τ C S χ e.val)/(M : ℝ) := by
  unfold kernelAbsoluteMass
  simp only [abs_of_nonneg (latentCandidateKernel_nonneg B L T H M τ C S χ hχ _ _),
    Fintype.card_fin]
  exact congrArg (fun x : ℝ => x/(M : ℝ)) (candidateMatrix_total _ _ _)

theorem endpoint_origin_cutNorm_bound {B L T H M N u : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (S : Fin M → Finset ℕ) :
    kernelCutNorm (fun i k =>
      latentCandidateKernel B L T H M τ C S (endpointRampedCutoff B T N u δ) i k-
      latentCandidateKernel B L T H M τ C S
        (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) i k) ≤
      ((M : ℝ)/((T : ℝ)*(N+1)*δ))*
        kernelAbsoluteMass (latentCandidateKernel B L T H M τ C S (smoothCandidateCutoff B T)) := by
  let r : ℝ := (M : ℝ)/((T : ℝ)*(N+1)*δ)
  have hw (e : BlockCandidateIndex M) :
      |candidateMeanWeight B L τ C S (endpointRampedCutoff B T N u δ) e-
        candidateMeanWeight B L τ C S
          (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) e| ≤
        r*candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e := by
    rw [candidateMeanWeight_cutoff_error]
    have hf : |endpointRampedCutoff B T N u δ e-
        rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1))) e| ≤
        smoothCandidateCutoff B T e*r := by
      change |smoothCandidateCutoff B T e*countingRamp δ _ _-
        smoothCandidateCutoff B T e*countingRamp δ _ _| ≤ _
      rw [← mul_sub,abs_mul,abs_of_nonneg (smoothCandidateCutoff_nonneg B T e)]
      exact mul_le_mul_of_nonneg_left
        (countingRamp_block_shift hδ hT N u e.1.1 _) (smoothCandidateCutoff_nonneg B T e)
    exact (mul_le_mul_of_nonneg_left hf
      (candidateMeanWeight_nonneg B L τ C S (fun _ => 1) (fun _ => zero_le_one) e)).trans_eq (by
        rw [candidateMeanWeight_cutoff_factor B L τ C S (smoothCandidateCutoff B T) e]
        ring)
  calc
    _ ≤ (2*∑ e : blockCandidates B L T H M τ C S,
        |candidateMeanWeight B L τ C S (endpointRampedCutoff B T N u δ) e.val-
          candidateMeanWeight B L τ C S
            (rampedCandidateCutoff B T δ ((u : ℝ)/((T : ℝ)*(N+1)))) e.val|)/(M : ℝ) :=
      latentCandidateKernel_cutNorm_sub _ _ _ _ _ _ _ _ _ _
    _ ≤ (2*∑ e : blockCandidates B L T H M τ C S,
        r*candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e.val)/(M : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun e _ => hw e.val)) (by norm_num)
    _ = _ := by
      rw [latentCandidateKernel_absoluteMass S _ (smoothCandidateCutoff_nonneg B T),← mul_sum]
      dsimp only [r]
      ring

end JointDickman

end OAI
