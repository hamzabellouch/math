import OAI.NumberTheory.JointDickman.Amplification.CandidateScalarSum

namespace OAI

/-! # The latent candidate kernel is the regularized arithmetic fair-split sum -/

namespace JointDickman
open Finset

open Classical in
noncomputable def regularRetainedArithmeticKernel (B L j : ℕ) (τ C : ℝ)
    (T V : ℕ) (S R : Finset ℕ) : ℝ :=
  B*∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    ∑ c ∈ Ioc 0 V, subsetRetentionMass S A*subsetRetentionMass R D*
      (if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
          (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
        regularArithmeticScalar B L j τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p)
      else 0)

open Classical in
/-- Exact normalization of the smooth latent kernel. In particular, its
arithmetic coefficient, coprimality, endpoint and remainder restrictions
are all the same ones estimated separately in the regularity argument. -/
theorem candidateSiteKernel_eq_regularArithmetic {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 1 < B) (hT : 0 < T)
    (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    (i t : Fin M) (hit : i < t)
    (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    {S R : Finset ℕ} (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C
      (candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)) i t S R =
      independentRootMean B L τ C*
        regularRetainedArithmeticKernel B L (t.val-i.val) τ C T V S R := by
  rw [candidateSiteKernel_fair_sum hB _ i t hit hS hR]
  unfold regularRetainedArithmeticKernel
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  have hp :
      (if BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) ∧
          (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
          (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
        regularCoefficientWeight B L τ C (candidateQuotient ((i,t),(A,D)))*
          candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) ((i,t),(A,D))
      else 0) =
      ∑ c ∈ Ioc 0 V,
        if (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
            (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D)) then
          regularArithmeticScalar B L (t.val-i.val) τ C T c (∏ p ∈ A,p) (∏ p ∈ D,p)
        else 0 := by
    by_cases hr : (RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A)) ∧
        (RegularPrimeSet B L τ C D ∧ RegularPrimeSet B L τ C (R \ D))
    · simp only [hr,and_true,ite_true]
      exact regularCandidateScalar_eq_sum (by omega) hT hV hit hH hjT
    · simp only [hr,and_false,ite_false,sum_const_zero]
  rw [hp]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro c _
  ring

end JointDickman

end OAI
