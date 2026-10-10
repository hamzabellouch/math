import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingProgram
import OAI.Combinatorics.ContingencyTables.Sampling.UnitTrialSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicSemantics

namespace OAI

/-! # One executable program chooses the correct rectangle branch -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] unitProfileRetry unitCodeOuterDraw
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma hasLargeRectangle_spec (k : ℕ) :
    hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true ↔
      0<(largeIndices (d^20,List.ofFn r)).length ∧
      0<(largeIndices (d^20,List.ofFn c)).length := by
  simp only [hasLargeRectangle,parameterLargeIndices,marginThreshold_ofFn,
    ite_true,Bool.false_eq_true,ite_false,Bool.and_eq_true,decide_eq_true_eq]

lemma allSmall_of_no_large (k : ℕ)
    (h : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)≠true) :
    ∀ i j,paperSmall r c i j=true := by
  intro i j
  apply Bool.eq_true_of_ne_false
  intro hij
  obtain ⟨hi,hj⟩ := (firstPaperSmall_false_iff r c (d^20) i j).mp hij
  have a := (largeIndexEquiv r (d^20)).symm ⟨i,hi⟩
  have b' := (largeIndexEquiv c (d^20)).symm ⟨j,hj⟩
  apply h
  apply (hasLargeRectangle_spec r c k).mpr
  exact ⟨Nat.zero_lt_of_lt a.isLt,Nat.zero_lt_of_lt b'.isLt⟩

lemma parameterUnitWords_ofFn (k : ℕ) :
    parameterUnitWords ((List.ofFn r,List.ofFn c),k)=outerTrials d k*(outerSteps d b k*s) := by
  rw [parameterUnitWords,parameterTrials_ofFn,parameterSteps_ofFn,parameterProposalWidth_ofFn]

lemma unitCodeBits_le (k : ℕ) : outerTrials d k*(outerSteps d b k*s)≤finiteSamplerBits r c k := by
  apply Nat.mul_le_mul_left
  exact (Nat.mul_le_mul_left (outerSteps d b k)
    (Nat.le_add_right s (25*(d+b+outerAccuracy d b k+1)^62))).trans (Nat.le_add_right _ _)

lemma scheduled_steps_pos (k : ℕ) : 0<outerSteps d b k := by
  have hd : 0<d := by unfold dimensionAllowance; omega
  have hb := (smallBinaryLength_parameters r c).2.1
  unfold outerSteps
  exact Nat.mul_pos (pow_pos hd _) (pow_pos (by omega) _)

/-- The all-small branch uses a prefix of the same public fixed-length word. -/
lemma unitSamplingMatrix_code (hsmall : ∀ i j,paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) (bits : Fin (finiteSamplerBits r c k) → Bool) :
    unitSamplingMatrix (((List.ofFn r,List.ofFn c),k),List.ofFn bits)=
      matrixCode (unitCodeOuterDraw r c (computedCellEquiv r c) (allSmallFibre r c hsmall)
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
        (GreedyFeasibleTable.table r c htotal) (prefixWord (unitCodeBits_le r c k) bits)).val := by
  have hdraw := unitProfileRetry_code r c (computedCellEquiv r c) hsmall htotal
    (outerAccuracy d b k) (tableState r c (GreedyFeasibleTable.table r c htotal))
    (outerSteps d b k) (outerTrials d k) (25*(d+b+outerAccuracy d b k+1)^62)
    (scheduled_steps_pos r c k) (GreedyFeasibleTable.table r c htotal)
    (prefixWord (unitCodeBits_le r c k) bits)
  unfold unitSamplingMatrix unitSamplingInput unitSamplingBits samplingRetryParameters
  rw [parameterUnitWords_ofFn,take_ofFn_prefix (unitCodeBits_le r c k),
    initialConfiguration_code r c htotal,samplingSchedule_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  have hcode : matrixCode (GreedyFeasibleTable.table r c htotal).val=
      List.ofFn (fun i => List.ofFn (GreedyFeasibleTable.matrix r c i)) := rfl
  rw [hcode] at hdraw
  simpa only [Table] using hdraw

end
end ContingencyTables.SmallGraphProfiles

end OAI
