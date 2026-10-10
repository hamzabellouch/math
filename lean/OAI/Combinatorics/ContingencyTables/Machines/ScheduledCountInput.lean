import OAI.Combinatorics.ContingencyTables.Sampling.OriginalOuterVector
import OAI.Combinatorics.ContingencyTables.Sampling.UnitOuterVector
import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileScheduleSemantics
import OAI.Combinatorics.ContingencyTables.Transport.UnaryMarkers

namespace OAI

/-! # Supplying the finite count evaluator from the public sampling parameters -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] initialCheck marginPadding parameterDimension parameterAccuracy
  parameterCompletionWidth parameterSteps parameterProposalWidth hasLargeRectangle parameterTrials
  profileBoxIndex outerVector UnitCountPrograms.outerVector

/-- The same cache parameters used by the executed approximate sampler. -/
def scheduledCacheParameters (z : SamplingParameters) : TransitionCacheParameters :=
  (((initialCheck z.1,marginPadding z.1),(parameterDimension z,parameterAccuracy z)),
    parameterCompletionWidth z)

def scheduledCacheParametersRealizer : Realizer scheduledCacheParameters :=
  pair (pair (pair (composition (f := fun z : SamplingParameters => z.1) (g := initialCheck) first initialCheckRealizer)
    (composition (f := fun z : SamplingParameters => z.1) (g := marginPadding) first marginPaddingRealizer))
    (pair parameterDimensionRealizer parameterAccuracyRealizer)) parameterCompletionWidthRealizer

lemma polynomial_scheduledCacheParameters : PolynomialTime scheduledCacheParametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_initialCheck)
    (polynomial_composition polynomial_first polynomial_marginPadding))
    (polynomial_pair polynomial_parameterDimension polynomial_parameterAccuracy))
    polynomial_parameterCompletionWidth

def scheduledDenseWidth (z : SamplingParameters) : ℕ :=
  parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z)+parameterCompletionWidth z

def scheduledDenseWidthRealizer : Realizer scheduledDenseWidth :=
  composition (f := fun z : SamplingParameters =>
    (parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z),parameterCompletionWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := fun z : SamplingParameters =>
      (parameterSteps z,parameterProposalWidth z+parameterCompletionWidth z))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair parameterStepsRealizer (composition
        (f := fun z : SamplingParameters => (parameterProposalWidth z,parameterCompletionWidth z))
        (g := fun p : ℕ×ℕ => p.1+p.2)
        (pair parameterProposalWidthRealizer parameterCompletionWidthRealizer) add)) multiply)
      parameterCompletionWidthRealizer) add

lemma polynomial_scheduledDenseWidth : PolynomialTime scheduledDenseWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_parameterSteps (polynomial_composition
      (polynomial_pair polynomial_parameterProposalWidth polynomial_parameterCompletionWidth)
      polynomial_add)) polynomial_multiply) polynomial_parameterCompletionWidth) polynomial_add

def scheduledUnitWidth (z : SamplingParameters) : ℕ := parameterSteps z*parameterProposalWidth z

def scheduledUnitWidthRealizer : Realizer scheduledUnitWidth :=
  composition (f := fun z : SamplingParameters => (parameterSteps z,parameterProposalWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair parameterStepsRealizer parameterProposalWidthRealizer) multiply

lemma polynomial_scheduledUnitWidth : PolynomialTime scheduledUnitWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_parameterSteps polynomial_parameterProposalWidth)
    polynomial_multiply

attribute [local irreducible] scheduledDenseWidth scheduledUnitWidth

/-- The all-small branch uses only the proposal bits of each walk. -/
def scheduledTrialWidth (z : SamplingParameters) : ℕ :=
  if hasLargeRectangle z then scheduledDenseWidth z else scheduledUnitWidth z

def scheduledTrialWidthRealizer : Realizer scheduledTrialWidth :=
  choose hasLargeRectangleRealizer scheduledDenseWidthRealizer scheduledUnitWidthRealizer

lemma polynomial_scheduledTrialWidth : PolynomialTime scheduledTrialWidthRealizer :=
  polynomial_choose polynomial_hasLargeRectangle polynomial_scheduledDenseWidth polynomial_scheduledUnitWidth

attribute [local irreducible] scheduledTrialWidth

/-- Numeric loop lengths are charged explicitly, in addition to binary input size. -/
def scheduledCountInputMeasure (z : SamplingParameters) : ℕ :=
  parameterSteps z+parameterTrials z+parameterProposalWidth z+scheduledTrialWidth z+weight z

lemma weight_le_scheduledCountInputMeasure (z : SamplingParameters) :
    weight z ≤ X.eval (scheduledCountInputMeasure z) := by
  simp only [eval_X,scheduledCountInputMeasure]
  omega

def scheduledMatrixParameters (z : SamplingParameters) : MatrixParameters :=
  (scheduledCacheParameters z,unaryMarkers (parameterProposalWidth z))

def scheduledMatrixParametersRealizer : Realizer scheduledMatrixParameters :=
  pair scheduledCacheParametersRealizer
    (composition (f := parameterProposalWidth) (g := unaryMarkers)
      parameterProposalWidthRealizer unaryMarkersRealizer)

attribute [local irreducible] scheduledMatrixParameters

lemma work_scheduledMatrixParameters :
    WorkBound scheduledMatrixParametersRealizer scheduledCountInputMeasure := by
  unfold scheduledMatrixParametersRealizer scheduledMatrixParameters
  have hm : WorkBound (composition parameterProposalWidthRealizer unaryMarkersRealizer)
      scheduledCountInputMeasure := by
    apply work_composition (work_of_polynomial polynomial_parameterProposalWidth X
      weight_le_scheduledCountInputMeasure) work_unaryMarkers X
    intro z
    simp only [id_eq,eval_X,scheduledCountInputMeasure]
    omega
  exact work_pair (work_of_polynomial polynomial_scheduledCacheParameters X
    weight_le_scheduledCountInputMeasure) hm X weight_le_scheduledCountInputMeasure

def scheduledStartIndex (z : SamplingParameters) : ℕ := profileBoxIndex (initialCheck z.1)

def scheduledStartIndexRealizer : Realizer scheduledStartIndex :=
  composition (composition (f := fun z : SamplingParameters => z.1) (g := initialCheck) first initialCheckRealizer) profileBoxIndexRealizer

lemma polynomial_scheduledStartIndex : PolynomialTime scheduledStartIndexRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_initialCheck)
    polynomial_profileBoxIndex

def scheduledWalkInput (z : SamplingParameters) : WalkCountInput :=
  (scheduledMatrixParameters z,(parameterSteps z,scheduledStartIndex z))

def scheduledWalkInputRealizer : Realizer scheduledWalkInput :=
  pair scheduledMatrixParametersRealizer (pair parameterStepsRealizer scheduledStartIndexRealizer)

attribute [local irreducible] scheduledWalkInput

lemma work_scheduledWalkInput : WorkBound scheduledWalkInputRealizer scheduledCountInputMeasure := by
  unfold scheduledWalkInputRealizer scheduledWalkInput
  exact work_pair work_scheduledMatrixParameters
    (work_of_polynomial (polynomial_pair polynomial_parameterSteps polynomial_scheduledStartIndex)
      X weight_le_scheduledCountInputMeasure) X weight_le_scheduledCountInputMeasure

def scheduledTrialInput (z : SamplingParameters) : TrialVectorInput := (scheduledWalkInput z,z.1)

def scheduledTrialInputRealizer : Realizer scheduledTrialInput := pair scheduledWalkInputRealizer first

attribute [local irreducible] scheduledTrialInput

lemma work_scheduledTrialInput : WorkBound scheduledTrialInputRealizer scheduledCountInputMeasure := by
  unfold scheduledTrialInputRealizer scheduledTrialInput
  exact work_pair work_scheduledWalkInput (work_of_polynomial polynomial_first X
    weight_le_scheduledCountInputMeasure) X weight_le_scheduledCountInputMeasure

def scheduledTrialDenominator (z : SamplingParameters) : ℕ :=
  BinaryPowerPrograms.power (2,scheduledTrialWidth z)

def scheduledTrialDenominatorRealizer : Realizer scheduledTrialDenominator :=
  composition (f := fun z : SamplingParameters => (2,scheduledTrialWidth z))
    (g := BinaryPowerPrograms.power)
    (pair (constant 2) scheduledTrialWidthRealizer) BinaryPowerPrograms.powerRealizer

attribute [local irreducible] scheduledTrialDenominator

lemma work_scheduledTrialDenominator :
    WorkBound scheduledTrialDenominatorRealizer scheduledCountInputMeasure := by
  unfold scheduledTrialDenominatorRealizer scheduledTrialDenominator
  apply work_composition (work_of_polynomial
    (polynomial_pair (polynomial_constant 2) polynomial_scheduledTrialWidth)
      X weight_le_scheduledCountInputMeasure) BinaryPowerPrograms.work_power (X+C (weight (2:ℕ)))
  intro z
  simp only [eval_add,eval_X,eval_C,scheduledCountInputMeasure]
  omega

def scheduledOuterInput (z : SamplingParameters) : OuterVectorInput :=
  (scheduledTrialInput z,((unaryMarkers (parameterTrials z),scheduledTrialDenominator z),
    GreedyFeasibleTable.listMatrix z.1.1 z.1.2))

def scheduledOuterInputRealizer : Realizer scheduledOuterInput :=
  pair scheduledTrialInputRealizer
    (pair (pair (composition (f := parameterTrials) (g := unaryMarkers)
      parameterTrialsRealizer unaryMarkersRealizer) scheduledTrialDenominatorRealizer)
      (composition (f := fun z : SamplingParameters => z.1)
        (g := fun p => GreedyFeasibleTable.listMatrix p.1 p.2) first GreedyFeasibleTable.tableRealizer))

attribute [local irreducible] scheduledOuterInput

lemma work_scheduledOuterInput : WorkBound scheduledOuterInputRealizer scheduledCountInputMeasure := by
  unfold scheduledOuterInputRealizer scheduledOuterInput
  have hm : WorkBound (composition parameterTrialsRealizer unaryMarkersRealizer)
      scheduledCountInputMeasure := by
    apply work_composition (work_of_polynomial polynomial_parameterTrials X
      weight_le_scheduledCountInputMeasure) work_unaryMarkers X
    intro z
    simp only [id_eq,eval_X,scheduledCountInputMeasure]
    omega
  exact work_pair work_scheduledTrialInput
    (work_pair (work_pair hm work_scheduledTrialDenominator X weight_le_scheduledCountInputMeasure)
      (work_of_polynomial (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table)
        X weight_le_scheduledCountInputMeasure) X weight_le_scheduledCountInputMeasure)
    X weight_le_scheduledCountInputMeasure

/-- All first-success numerators, computed from the public binary margins. -/
def scheduledCounts (z : SamplingParameters) : List ℕ :=
  if hasLargeRectangle z then outerVector (scheduledOuterInput z)
  else UnitCountPrograms.outerVector (scheduledOuterInput z)

def scheduledCountsRealizer : Realizer scheduledCounts :=
  choose hasLargeRectangleRealizer
    (composition (f := scheduledOuterInput) (g := outerVector)
      scheduledOuterInputRealizer outerVectorRealizer)
    (composition (f := scheduledOuterInput) (g := UnitCountPrograms.outerVector)
      scheduledOuterInputRealizer UnitCountPrograms.outerVectorRealizer)

attribute [local irreducible] scheduledCounts

def scheduledCountsMeasure (z : SamplingParameters) : ℕ := scheduledCountInputMeasure z+
  outerVectorMeasure (scheduledOuterInput z)+UnitCountPrograms.outerVectorMeasure (scheduledOuterInput z)

lemma work_scheduledCounts : WorkBound scheduledCountsRealizer scheduledCountsMeasure := by
  have hi (z : SamplingParameters) : scheduledCountInputMeasure z ≤ X.eval (scheduledCountsMeasure z) := by
    simp only [eval_X,scheduledCountsMeasure]
    omega
  have hb := work_remeasure work_scheduledOuterInput X hi
  have hw (z : SamplingParameters) : weight z ≤ X.eval (scheduledCountsMeasure z) :=
    (weight_le_scheduledCountInputMeasure z).trans (by simpa only [eval_X] using hi z)
  unfold scheduledCountsRealizer scheduledCounts
  apply work_choose (work_of_polynomial polynomial_hasLargeRectangle X hw)
  · apply work_composition hb work_outerVector X
    intro z
    simp only [eval_X,scheduledCountsMeasure]
    omega
  · apply work_composition hb UnitCountPrograms.work_outerVector X
    intro z
    simp only [eval_X,scheduledCountsMeasure]
    omega
  · exact hw

end ContingencyTables.ProfilePrograms

end OAI
