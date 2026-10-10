import OAI.NumberTheory.JointDickman.Amplification.CandidateProductMean

namespace OAI

/-! # Product-dependent cutoffs in the exact candidate mean -/
namespace JointDickman
open Finset

noncomputable def weightedCandidateRetained (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (q : ℕ → ℕ → ℝ) (A D : Finset ℕ) : ℝ :=
  candidateRetainedWeight B L j τ C T V A D*q (∏ p ∈ D,p) (∏ p ∈ A,p)

open Classical in
theorem weightedCandidateRetained_mean (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (q : ℕ → ℕ → ℝ) (g h : Finset ℕ → ℝ) :
    subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
      (weightedCandidateRetained B L j τ C T V q)) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        if b.Coprime a then signedSplitProductMass (auxiliaryPrimes B) h a*
          signedSplitProductMass (auxiliaryPrimes B) g b*
          (regularizedProductWeight B L j τ C T V a b*q a b) else 0 := by
  have hk : retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q) =
      retainedSubsetKernel (auxiliaryPrimes B) (fun A D =>
        if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
          regularizedProductWeight B L j τ C T V (∏ p ∈ D,p) (∏ p ∈ A,p)*
            q (∏ p ∈ D,p) (∏ p ∈ A,p) else 0) := by
    funext S R
    unfold retainedSubsetKernel
    apply sum_congr rfl
    intro A hA
    apply sum_congr rfl
    intro D hD
    rw [weightedCandidateRetained,candidateRetainedWeight_eq_product B L j τ C T V
      (mem_powerset.mp hA) (mem_powerset.mp hD)]
    dsimp only
    by_cases hc : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p)
    · rw [ite_eq_left hc,ite_eq_left hc]
    · rw [ite_eq_right hc,ite_eq_right hc,zero_mul]
  rw [hk,subsetKernel_product_mean B g h (fun b a =>
    if b.Coprime a then regularizedProductWeight B L j τ C T V a b*q a b else 0),sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hc : b.Coprime a
  · rw [ite_eq_left hc,ite_eq_left hc]
    ring
  · rw [ite_eq_right hc,ite_eq_right hc,mul_zero]

open Classical in
noncomputable def weightedAmplificationArithmeticSum (B j : ℕ) (T : ℝ) (U V : ℕ)
    (q : ℕ → ℕ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    amplificationArithmeticTerm B j T g h c b a*q a b

open Classical in
noncomputable def weightedRegularizedArithmeticSum (B L j : ℕ) (τ C T : ℝ) (U V : ℕ)
    (q : ℕ → ℕ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    if coefficientTripleRegular B L τ C a b c then
      amplificationArithmeticTerm B j T g h c b a*q a b else 0

open Classical in
theorem weightedRegularizedArithmeticSum_eq_product (B L j : ℕ) (τ C : ℝ)
    (T U V : ℕ) (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U)
    (q : ℕ → ℕ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    weightedRegularizedArithmeticSum B L j τ C T U V q g h =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        (regularizedProductWeight B L j τ C T V a b*q a b) := by
  rw [← signedProductPair_sum_on (auxiliaryPrimes B) _ _ _ (Ioc 0 U)
    (primeSplitProductSupport_subset_Ioc (auxiliaryPrimes_prime B) hU)]
  unfold weightedRegularizedArithmeticSum regularizedProductWeight
  simp_rw [amplificationArithmeticTerm_factor,mul_sum,sum_mul]
  conv_lhs => arg 2; ext c; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext a; rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [mul_sum]
  apply sum_congr rfl
  intro c _
  split_ifs <;> ring

open Classical in
theorem weighted_amplification_regularization_error (B L j : ℕ) (τ C T : ℝ) (U V : ℕ)
    (q : ℕ → ℕ → ℝ) (hq : ∀ a b, |q a b| ≤ 1)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    |weightedAmplificationArithmeticSum B j T U V q g h-
        weightedRegularizedArithmeticSum B L j τ C T U V q g h| ≤
      ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        discardedAmplificationTerm B L j τ C T g h c b a := by
  unfold weightedAmplificationArithmeticSum weightedRegularizedArithmeticSum
  simp_rw [mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro c _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro b _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a _
  unfold discardedAmplificationTerm
  split_ifs
  · simp
  · simp only [mul_zero,sub_zero]
    rw [← mul_assoc,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hq a b) (abs_nonneg _)).trans_eq (mul_one _)

end JointDickman

end OAI
