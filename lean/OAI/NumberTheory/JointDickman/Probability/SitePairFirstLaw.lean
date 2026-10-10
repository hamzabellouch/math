import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitProduct

namespace OAI

/-! # The first coefficient and remaining sets at two independent sites -/

namespace JointDickman
open Finset

theorem sitePair_first_law (P : Finset ℕ)
    (H : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
        sitePairSplitAverage P S T (fun A D => H A (S \ A) D (T \ D))) =
    ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      ∑ R ∈ P.powerset, ∑ Q ∈ P.powerset,
        fairSelectedRemainingMass P A R * fairSelectedRemainingMass P D Q * H A R D Q := by
  unfold sitePairSplitAverage
  simp only [mul_sum]
  conv_lhs => arg 2; ext S; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext A; arg 2; ext S; rw [sum_comm]
  conv_lhs => arg 2; ext A; rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
        subsetRetentionMass S A * (∑ T ∈ P.powerset,
          bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T * subsetRetentionMass T D * H A (S \ A) D (T \ D)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro T _
      ring
    _ = ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R *
        (∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
          subsetRetentionMass T D * H A R D (T \ D)) :=
      first_split_reindex P A (mem_powerset.mp hA) (fun R =>
        ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
          subsetRetentionMass T D * H A R D (T \ D))
    _ = ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R *
        (∑ Q ∈ P.powerset, fairSelectedRemainingMass P D Q * H A R D Q) := by
      apply sum_congr rfl
      intro R _
      rw [first_split_reindex P D (mem_powerset.mp hD) (fun Q => H A R D Q)]
    _ = _ := by simp only [mul_sum, mul_assoc]

end JointDickman

end OAI
