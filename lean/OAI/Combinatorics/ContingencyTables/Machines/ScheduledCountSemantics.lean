import OAI.Combinatorics.ContingencyTables.Machines.ScheduledCountInput
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalBoxPush
import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingAccuracy

namespace OAI

/-! # The scheduled executable numerator vector is the public sampler's law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] scheduledTrialDenominator scheduledTrialWidth
  scheduledCounts scheduledOuterInput listedOuterCounts unitOuterCounts matrixInput
  scheduledTableDraw listedOuterDraw unitCodeOuterDraw

private lemma dyadic_trialDenom (N s f : ℕ) :
    (2:ℕ)^(N*(s+f)+f)=(2^(s+f))^N*2^f := by
  rw [pow_add,←pow_mul]
  congr 2
  exact Nat.mul_comm _ _


variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma scheduledTrialDenominator_dense (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true) :
    scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k)=
      (2^(s+25*(d+b+outerAccuracy d b k+1)^62))^(outerSteps d b k)*
        2^(25*(d+b+outerAccuracy d b k+1)^62) := by
  rw [scheduledTrialDenominator,BinaryPowerPrograms.power_eq,scheduledTrialWidth,hlarge]
  simp only [ite_true,scheduledDenseWidth,parameterSteps_ofFn,parameterProposalWidth_ofFn,parameterCompletionWidth_ofFn]
  exact dyadic_trialDenom _ _ _

lemma scheduledTrialDenominator_unit (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)≠true) :
    scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k)=(2^s)^(outerSteps d b k) := by
  rw [scheduledTrialDenominator,BinaryPowerPrograms.power_eq,scheduledTrialWidth,ite_eq_right hlarge]
  rw [scheduledUnitWidth,parameterSteps_ofFn,parameterProposalWidth_ofFn,←pow_mul,Nat.mul_comm]

lemma scheduledTrialDenominator_pos (z : SamplingParameters) : 0<scheduledTrialDenominator z := by
  rw [scheduledTrialDenominator,BinaryPowerPrograms.power_eq]
  positivity

lemma scheduledOuterInput_code (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    scheduledOuterInput ((List.ofFn r,List.ofFn c),k)=
      (((matrixInput r c (computedCellEquiv r c) b (outerAccuracy d b k)
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (unaryMarkers s),
        (outerSteps d b k,(profileIndex r c (computedCellEquiv r c)
          (tableState r c (GreedyFeasibleTable.table r c htotal))).val)),
        (List.ofFn r,List.ofFn c)),
        ((unaryMarkers (outerTrials d k),scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k)),
          matrixCode (GreedyFeasibleTable.table r c htotal).val)) := by
  unfold scheduledOuterInput scheduledTrialInput scheduledWalkInput scheduledMatrixParameters
    scheduledCacheParameters scheduledStartIndex
  rw [initialCheck_code r c htotal,marginPadding_ofFn,parameterDimension_ofFn,
    parameterAccuracy_ofFn,parameterCompletionWidth_ofFn,parameterProposalWidth_ofFn,
    parameterSteps_ofFn,profileBoxIndex_actual,parameterTrials_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  unfold matrixInput
  rfl

/-- No extra table oracle: this is the integer law of the ordinary public branch. -/
def scheduledCountsLaw (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    IntegerLaw (Table r c)
      ((scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k))^(outerTrials d k)) :=
  if hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true then
    (listedOuterCounts r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp hlarge).1 ((hasLargeRectangle_spec r c k).mp hlarge).2
      b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
      (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
      (GreedyFeasibleTable.table r c htotal)).rebase
      (congrArg (fun Q => Q^(outerTrials d k)) (scheduledTrialDenominator_dense r c k hlarge).symm)
  else
    (unitOuterCounts r c (computedCellEquiv r c) (allSmall_of_no_large r c k hlarge)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
      (GreedyFeasibleTable.table r c htotal)).rebase
      (congrArg (fun Q => Q^(outerTrials d k)) (scheduledTrialDenominator_unit r c k hlarge).symm)

lemma scheduledDraw_dense (htotal : ∑ i,r i=∑ j,c j) (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true) :
    scheduledTableDraw r c htotal k=
      listedOuterDraw r c (computedCellEquiv r c)
        ((hasLargeRectangle_spec r c k).mp hlarge).1 ((hasLargeRectangle_spec r c k).mp hlarge).2
        b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
        (GreedyFeasibleTable.table r c htotal) := by
  funext bits
  unfold scheduledTableDraw
  rw [dite_eq_left hlarge]

lemma scheduledDraw_unit (htotal : ∑ i,r i=∑ j,c j) (k : ℕ)
    (hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)≠true) :
    scheduledTableDraw r c htotal k=fun bits =>
      unitCodeOuterDraw r c (computedCellEquiv r c) (allSmallFibre r c (allSmall_of_no_large r c k hlarge))
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
        (GreedyFeasibleTable.table r c htotal) (prefixWord (unitCodeBits_le r c k) bits) := by
  funext bits
  unfold scheduledTableDraw
  rw [dite_eq_right hlarge]

lemma scheduledCountsLaw_law (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    (scheduledCountsLaw r c htotal k).toRational
      (pow_pos (scheduledTrialDenominator_pos _) _)=
      mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
        (scheduledTableDraw r c htotal k) := by
  unfold scheduledCountsLaw
  split_ifs with hlarge
  · rw [scheduledDraw_dense r c htotal k hlarge]
    exact (IntegerLaw.toRational_rebase _ _ (by positivity) _).trans
      (listedOuterCounts_law r c _ _ _ _ _ _ htotal _ _ _ _)
  · rw [scheduledDraw_unit r c htotal k hlarge]
    exact (IntegerLaw.toRational_rebase _ _ (by positivity) _).trans
      ((unitOuterCounts_law r c _ htotal _ _ _ _ _).trans
        (padded_draw_law (unitCodeBits_le r c k) _).symm)

/-- Every literal vector entry equals the corresponding embedded table count,
including zero at infeasible matrices in the original bounding box. -/
lemma scheduledCounts_actual (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    scheduledCounts ((List.ofFn r,List.ofFn c),k)=
      List.ofFn (((scheduledCountsLaw r c htotal k).push (index r c le_rfl)).count) := by
  unfold scheduledCounts
  by_cases hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true
  · rw [ite_eq_left hlarge,scheduledOuterInput_code r c htotal]
    conv_lhs => rw [scheduledTrialDenominator_dense r c k hlarge]
    rw [outerVector_actual r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp hlarge).1 ((hasLargeRectangle_spec r c k).mp hlarge).2
      b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1 htotal _ _
        (unaryMarkers_length _) _ _ _]
    apply congrArg List.ofFn
    funext j
    rw [OriginalBoxLaw.retry_count_some,OriginalBoxLaw.push_count]
    simp only [scheduledCountsLaw,dite_eq_left hlarge,IntegerLaw.rebase,listedOuterCounts]
    simp only [IntegerLaw.retry,unaryMarkers_length]
  · rw [ite_eq_right hlarge,scheduledOuterInput_code r c htotal]
    conv_lhs => rw [scheduledTrialDenominator_unit r c k hlarge]
    rw [unit_outerVector_actual r c (computedCellEquiv r c) b (outerAccuracy d b k)
      (allSmall_of_no_large r c k hlarge) htotal _ _ (unaryMarkers_length _) _ _ _]
    apply congrArg List.ofFn
    funext j
    rw [OriginalBoxLaw.retry_count_some,OriginalBoxLaw.push_count]
    simp only [scheduledCountsLaw,dite_eq_right hlarge,IntegerLaw.rebase,unitOuterCounts]
    simp only [IntegerLaw.retry,unaryMarkers_length]

end
end ContingencyTables.SmallGraphProfiles

end OAI
