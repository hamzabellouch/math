import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitSums

namespace OAI

/-! # Conditional products of the two independent fair splits -/

namespace JointDickman
open Finset

noncomputable def sitePairSplitAverage (P S T : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ C ∈ P.powerset,
    subsetRetentionMass S A * subsetRetentionMass T C * F A C

/-- Given the two sites, the two fair splits are independent. -/
theorem twoSiteSplit_product (P : Finset ℕ)
    (F G : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.site₁.val x.site₂.val x.first₁.val x.first₂.val *
      G x.site₁.val x.site₂.val x.second₁.val x.second₂.val) =
    ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
    ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
      (sitePairSplitAverage P S T (F S T) * sitePairSplitAverage P S T (G S T)) := by
  unfold twoSiteSplitMass
  rw [twoSiteSplit_sum P (fun S A D T C E =>
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
    subsetRetentionMass S A * subsetRetentionMass T C *
    subsetRetentionMass S D * subsetRetentionMass T E * F S T A C * G S T D E)]
  conv_rhs => arg 2; ext S; arg 2; arg 2; ext T; arg 2; rw [mul_comm]
  unfold sitePairSplitAverage
  simp only [sum_mul, mul_sum]
  apply sum_congr rfl
  intro S _
  conv_lhs => arg 2; ext A; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro C _
  apply sum_congr rfl
  intro D _
  apply sum_congr rfl
  intro E _
  ring

end JointDickman

end OAI
