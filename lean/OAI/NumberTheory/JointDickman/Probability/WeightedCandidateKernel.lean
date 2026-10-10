import OAI.NumberTheory.JointDickman.Amplification.WeightedCandidateProduct
import OAI.NumberTheory.JointDickman.Amplification.CandidateMeanBridge

namespace OAI

/-! # Exact latent candidate kernel with a product-dependent cutoff -/

namespace JointDickman
open Finset

open Classical in
theorem candidateSiteKernel_product_weight {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 1 < B) (hT : 0 < T) (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    (i t : Fin M) (hit : i < t) (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (q : ℕ → ℕ → ℝ)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C
      (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
        q (candidateHigh e) (candidateLow e)) i t S R =
      independentRootMean B L τ C*regularRemainderKernel B L τ C
        (weightedCandidateRetained B L (t.val-i.val) τ C T V q) S R := by
  rw [candidateSiteKernel_fair_sum hB _ i t hit hS hR]
  unfold regularRemainderKernel weightedCandidateRetained candidateRetainedWeight
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  have he := regularCandidateScalar_eq_sum (L := L) (τ := τ) (C := C) (by omega : 0 < B) hT hV (A := A) (D := D) hit hH hjT
  change (if BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) then
    regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D)) else 0) = _ at he
  by_cases ha : RegularPrimeSet B L τ C A
  all_goals by_cases hd : RegularPrimeSet B L τ C D
  all_goals by_cases hs : RegularPrimeSet B L τ C (S \ A)
  all_goals by_cases hr : RegularPrimeSet B L τ C (R \ D)
  all_goals simp only [ha,hd,hs,hr,and_self,and_true,and_false,
    ite_true,ite_false,mul_zero,zero_mul]
  by_cases had : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))
  · rw [ite_eq_left had] at he
    rw [ite_eq_left had,← mul_sum,← he]
    change _ = independentRootMean B L τ C*
      (subsetRetentionMass S A*subsetRetentionMass R D*
        (B*(regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
          candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D)))*
          q (candidateHigh ((i,t),(A,D))) (candidateLow ((i,t),(A,D)))))
    ring
  · rw [ite_eq_right had] at he
    rw [ite_eq_right had,← mul_sum,← he]
    simp only [mul_zero,zero_mul]

end JointDickman

end OAI
