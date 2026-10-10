import OAI.NumberTheory.JointDickman.Amplification.CandidatePairSum
import OAI.NumberTheory.JointDickman.Amplification.ReverseRowEnvelope
import OAI.NumberTheory.JointDickman.Amplification.IndependentRegularityLoss

namespace OAI

/-! # Domination of the actual latent candidate kernel by its row majorant -/

namespace JointDickman
open Finset

/-- Every actual candidate supplies one term of the fixed-endpoint box test. -/
theorem candidateMeanWeight_le_reverseEndpointTest {M B L T H : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e)
    (hχ : χ e ≤ 1) :
    candidateMeanWeight B L τ C S χ e ≤
      independentRootMean B L τ C/(B : ℝ)*
        (endpointSplitWeight B L τ C (S e.1.2) e.2.2*
          (endpointSplitWeight B L τ C (S e.1.1) e.2.1*
            reverseSupportedTest B T (candidateHigh e) (candidateLag e) (candidateLow e))) := by
  obtain ⟨_,_,_,hc,hrel,_,_,_,_,_,hclo,hchi,hblo,_,halo,hahi⟩ := he
  have ht := (regularCoefficientWeight_le B L τ C (candidateQuotient e)).trans
    (reverseSupportedTest_ge hB hT hTs hc hclo hchi halo hahi hrel hblo)
  let d := independentRootMean B L τ C/(B : ℝ)*
    (endpointSplitWeight B L τ C (S e.1.1) e.2.1*
      endpointSplitWeight B L τ C (S e.1.2) e.2.2)
  have hd : 0 ≤ d := mul_nonneg
    (div_nonneg (independentRootMean_nonneg _ _ _ _) (Nat.cast_nonneg B))
    (mul_nonneg (endpointSplitWeight_nonneg _ _ _ _ _ _) (endpointSplitWeight_nonneg _ _ _ _ _ _))
  have hreg := regularCoefficientWeight_nonneg B L τ C (candidateQuotient e)
  calc
    _ = (d*regularCoefficientWeight B L τ C (candidateQuotient e))*χ e := by
      rw [candidateMeanWeight_eq]
      dsimp [d,endpointSplitWeight,candidateLow,candidateHigh]
      ring
    _ ≤ d*regularCoefficientWeight B L τ C (candidateQuotient e) :=
      mul_le_of_le_one_right (mul_nonneg hd hreg) hχ
    _ ≤ d*reverseSupportedTest B T (candidateHigh e) (candidateLag e) (candidateLow e) :=
      mul_le_mul_of_nonneg_left ht hd
    _ = _ := by dsimp [d]; ring

/-- This is a pointwise comparison for the actual finite candidate list,
valid for every choice of the other endpoint types. -/
theorem latentCandidateKernel_le_reverseRowEnvelope {M B L T H : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (hχ : ∀ e, χ e ≤ 1) (i k : Fin M) (hik : i < k) :
    latentCandidateKernel B L T H M τ C S χ i k ≤
      reverseEndpointRowEnvelope B L T (k.val-i.val) τ C (S k) (S i) := by
  classical
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  unfold reverseEndpointRowEnvelope
  rw [sum_comm]
  simp_rw [mul_sum]
  apply sum_le_sum
  intro A _
  apply sum_le_sum
  intro D _
  split_ifs with he
  · exact candidateMeanWeight_le_reverseEndpointTest S χ hB hT hTs he (hχ _)
  · exact mul_nonneg
      (div_nonneg (independentRootMean_nonneg _ _ _ _) (Nat.cast_nonneg B))
      (mul_nonneg (endpointSplitWeight_nonneg _ _ _ _ _ _)
        (mul_nonneg (endpointSplitWeight_nonneg _ _ _ _ _ _)
          (reverseSupportedTest_nonneg _ _ _ _ _)))

end JointDickman

end OAI
