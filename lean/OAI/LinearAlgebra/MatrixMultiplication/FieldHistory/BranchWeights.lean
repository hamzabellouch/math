import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Support

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryBranchWeights

open AllFieldHistory AllFieldHistorySupport AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem stageB_branchPopulation_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℚ) =
      (population allocation dilation (.afterA h.val, phi) : ℚ) *
        stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) := by
  simp only [branchPopulation, Work.child, population_cast, amount, canonicalAmount, bAmount]
  ring

theorem stageB_branchPopulation_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℝ) =
      (population allocation dilation (.afterA h.val, phi) : ℝ) *
        (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ) := by
  exact_mod_cast stageB_branchPopulation_rat allocation dilation h b phi

theorem stageB_branchWeight_rat {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℚ) /
      (population allocation dilation (.afterA h.val, phi) : ℚ) =
        stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) := by
  have hpos := work_source_population_pos allocation hd (.stageB h, phi)
  have hden : (population allocation dilation (.afterA h.val, phi) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  apply (div_eq_iff hden).2
  rw [stageB_branchPopulation_rat]
  exact mul_comm _ _

theorem stageB_branchWeight_real {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (h : APositive K) (b : BSplit h) (phi : Placement) :
    (branchPopulation allocation dilation (.stageB h, phi) b : ℝ) /
      (population allocation dilation (.afterA h.val, phi) : ℝ) =
        (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ) := by
  have hpos := work_source_population_pos allocation hd (.stageB h, phi)
  have hden : (population allocation dilation (.afterA h.val, phi) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  apply (div_eq_iff hden).2
  rw [stageB_branchPopulation_real]
  exact mul_comm _ _

theorem shapeCounts_weighted_sum {I : Type*} [Fintype I]
    (code : I → JointPopulation.Shape) (weight : I → ℕ)
    (f : JointPopulation.Shape → ℝ) :
    (∑ u, (shapeCounts code weight u : ℝ) * f u) =
      ∑ b, (weight b : ℝ) * f (code b) := by
  simp only [shapeCounts, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [ite_mul]

end MatrixMultiplication.AllFieldHistoryBranchWeights

end

end OAI
