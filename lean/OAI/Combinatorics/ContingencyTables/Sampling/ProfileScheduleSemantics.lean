import OAI.Combinatorics.ContingencyTables.Sampling.ProfileSamplingProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRetrySemantics
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperFiniteSampler

namespace OAI

/-! # The computed schedule and initializer equal the proved sampler data -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] profileRetry listedOuterDraw tableState
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma marginDimension_ofFn : marginDimension (List.ofFn r,List.ofFn c)=d := by
  simp only [marginDimension,List.length_ofFn,dimensionAllowance,Fintype.card_fin]

lemma marginPadding_ofFn : marginPadding (List.ofFn r,List.ofFn c)=d^12 := by
  rw [marginPadding,marginDimension_ofFn]

lemma marginStateBound_ofFn : marginStateBound (List.ofFn r,List.ofFn c)=stateBound r c := by
  rw [marginStateBound,List.sum_ofFn,marginDimension_ofFn,marginPadding_ofFn,marginThreshold_ofFn]
  rfl

lemma marginBinaryLength_ofFn : marginBinaryLength (List.ofFn r,List.ofFn c)=b := by
  rw [marginBinaryLength,marginDimension_ofFn,marginStateBound_ofFn]
  rfl

lemma parameterDimension_ofFn (k : ℕ) : parameterDimension ((List.ofFn r,List.ofFn c),k)=d :=
  marginDimension_ofFn r c

lemma parameterBinaryLength_ofFn (k : ℕ) : parameterBinaryLength ((List.ofFn r,List.ofFn c),k)=b :=
  marginBinaryLength_ofFn r c

lemma parameterTrials_ofFn (k : ℕ) :
    parameterTrials ((List.ofFn r,List.ofFn c),k)=outerTrials d k := by
  rw [parameterTrials,parameterDimension_ofFn]
  rfl

lemma parameterSteps_ofFn (k : ℕ) :
    parameterSteps ((List.ofFn r,List.ofFn c),k)=outerSteps d b k := by
  rw [parameterSteps,parameterDimension_ofFn,parameterBinaryLength_ofFn]
  rfl

lemma parameterAccuracy_ofFn (k : ℕ) :
    parameterAccuracy ((List.ofFn r,List.ofFn c),k)=outerAccuracy d b k := by
  rw [parameterAccuracy,parameterDimension_ofFn,parameterBinaryLength_ofFn]
  rfl

lemma parameterProposalWidth_ofFn (k : ℕ) :
    parameterProposalWidth ((List.ofFn r,List.ofFn c),k)=smallProposalBits (I := Fin m) (J := Fin n) := by
  rw [parameterProposalWidth,parameterDimension_ofFn]

lemma parameterCompletionWidth_ofFn (k : ℕ) :
    parameterCompletionWidth ((List.ofFn r,List.ofFn c),k)=25*(d+b+outerAccuracy d b k+1)^62 := by
  rw [parameterCompletionWidth,parameterDimension_ofFn,parameterBinaryLength_ofFn,
    parameterAccuracy_ofFn]

lemma parameterWordCount_ofFn (k : ℕ) :
    parameterWordCount ((List.ofFn r,List.ofFn c),k)=finiteSamplerBits r c k := by
  rw [parameterWordCount,parameterTrials_ofFn,parameterSteps_ofFn,parameterProposalWidth_ofFn,
    parameterCompletionWidth_ofFn]

lemma initialConfiguration_code (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) :
    initialConfiguration ((List.ofFn r,List.ofFn c),k)=
      encodedConfiguration r c (computedCellEquiv r c) (outerAccuracy d b k)
        (tableState r c (GreedyFeasibleTable.table r c htotal))
        (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialConfiguration
  rw [initialCheck_code r c htotal,marginPadding_ofFn,parameterDimension_ofFn,
    parameterAccuracy_ofFn,initialViews_code r c htotal]
  rfl

lemma samplingSchedule_ofFn (k : ℕ) :
    samplingSchedule ((List.ofFn r,List.ofFn c),k)=
      ((outerSteps d b k,smallProposalBits (I := Fin m) (J := Fin n)),
        25*(d+b+outerAccuracy d b k+1)^62) := by
  rw [samplingSchedule,parameterSteps_ofFn,parameterProposalWidth_ofFn,parameterCompletionWidth_ofFn]

/-- Equality of the actual list program with the listed finite-word draw.
The current theorem is for the nonempty large-rectangle branch. -/
theorem samplingMatrix_code
    (hr : 0<(largeIndices (d^20,List.ofFn r)).length)
    (hc : 0<(largeIndices (d^20,List.ofFn c)).length)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) :
    samplingMatrix (((List.ofFn r,List.ofFn c),k),List.ofFn bits)=
      matrixCode (listedOuterDraw r c (computedCellEquiv r c) hr hc b (outerAccuracy d b k)
        (smallBinaryLength_parameters r c).1 (tableState r c (GreedyFeasibleTable.table r c htotal))
        (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits).val := by
  have hdraw := profileRetry_code r c (computedCellEquiv r c) hr hc b (outerAccuracy d b k)
    (smallBinaryLength_parameters r c).1 htotal
    (tableState r c (GreedyFeasibleTable.table r c htotal))
    (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits
  unfold samplingMatrix samplingRetryParameters
  rw [initialConfiguration_code r c htotal,samplingSchedule_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  have hcode : matrixCode (GreedyFeasibleTable.table r c htotal).val=
      List.ofFn (fun i => List.ofFn (GreedyFeasibleTable.matrix r c i)) := rfl
  rw [hcode] at hdraw
  dsimp only at hdraw ⊢
  exact hdraw

end
end ContingencyTables.SmallGraphProfiles

end OAI
