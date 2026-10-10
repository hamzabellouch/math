import OAI.NumberTheory.JointDickman.Amplification.WeightedCandidateMean
import OAI.NumberTheory.JointDickman.Counting.CountingArithmeticFeatures

namespace OAI

/-! # The actual candidate cutoff and its ramped arithmetic counterpart -/
namespace JointDickman
open Finset

noncomputable def rampedCandidateCutoff {M : ℕ} (B T : ℕ) (δ σ : ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
    countingRamp δ σ ((candidateLow e : ℝ)/(T*candidateQuotient e))

noncomputable def rampedProductCutoff (T j : ℕ) (δ σ : ℝ) (a b : ℕ) : ℝ :=
  countingRamp δ σ ((b : ℝ)/(T*((a-b)/j : ℕ)))

theorem rampedProductCutoff_bounds {δ : ℝ} (hδ : 0 < δ) (T j : ℕ) (σ : ℝ) (a b : ℕ) :
    0 ≤ rampedProductCutoff T j δ σ a b ∧ rampedProductCutoff T j δ σ a b ≤ 1 :=
  countingRamp_bounds hδ σ _

open Classical in
theorem candidateSiteKernel_pair_cutoff_congr {B L T H M : ℕ} {τ C : ℝ}
    (χ ψ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (hχ : ∀ A D, χ ((i,t),(A,D)) = ψ ((i,t),(A,D))) (S R : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      candidateSiteKernel B L T H M τ C ψ i t S R := by
  rw [candidateSiteKernel_factor_sum χ i t hit,candidateSiteKernel_factor_sum ψ i t hit]
  apply sum_congr rfl
  intro ab _
  unfold candidateCoefficientFactor
  rw [hχ]

theorem rampedCandidateCutoff_pair {M : ℕ} (B T : ℕ) (δ σ : ℝ)
    (i t : Fin M) (A D : Finset ℕ) :
    rampedCandidateCutoff B T δ σ ((i,t),(A,D)) =
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D))*
        rampedProductCutoff T (t.val-i.val) δ σ
          (candidateHigh ((i,t),(A,D))) (candidateLow ((i,t),(A,D))) := rfl

open Classical in
theorem rampedCandidateCutoff_bounds {M : ℕ} {δ : ℝ} (hδ : 0 < δ) (B T : ℕ)
    (σ : ℝ) (e : BlockCandidateIndex M) :
    0 ≤ rampedCandidateCutoff B T δ σ e ∧ rampedCandidateCutoff B T δ σ e ≤ 1 := by
  have hb : 0 ≤ candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e ∧
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e ≤ 1 := by
    unfold candidateCutoff amplificationOuterWeight amplificationInnerWeight
    have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    constructor
    · exact mul_nonneg (mul_nonneg h1.1 h2.1) h3.1
    · exact (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 zero_le_one) h3.2 h3.1
        (by norm_num)).trans_eq (by norm_num)
  have hr := countingRamp_bounds hδ σ ((candidateLow e : ℝ)/(T*candidateQuotient e))
  exact ⟨mul_nonneg hb.1 hr.1,
    (mul_le_mul hb.2 hr.2 hr.1 zero_le_one).trans_eq (one_mul _)⟩

open Classical in
theorem rampedArithmetic_eq_weighted (B j T U V : ℕ) (hj : 0 < j) (δ σ : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    rampedAmplificationArithmeticSum B j T U V δ σ g h =
      weightedAmplificationArithmeticSum B j T U V (rampedProductCutoff T j δ σ) g h := by
  unfold rampedAmplificationArithmeticSum weightedAmplificationArithmeticSum
  congr 1
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  by_cases he : a = b+j*c
  · have hq : (a-b)/j = c := by rw [he,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left c hj]
    simp only [rampedProductCutoff,hq]
  · simp only [amplificationArithmeticTerm,ite_eq_right he,zero_mul]

end JointDickman

end OAI
