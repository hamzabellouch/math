import OAI.Combinatorics.ContingencyTables.Sampling.UnitTrialProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicProgram

namespace OAI

/-! # A single computed sampler for large and all-small rectangles -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def parameterUnitWords (z : SamplingParameters) : ℕ :=
  parameterTrials z*(parameterSteps z*parameterProposalWidth z)
def parameterUnitWordsRealizer : Realizer parameterUnitWords :=
  composition (f := fun z : SamplingParameters =>
    (parameterTrials z,parameterSteps z*parameterProposalWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair parameterTrialsRealizer
      (composition (f := fun z : SamplingParameters => (parameterSteps z,parameterProposalWidth z))
        (g := fun p : ℕ×ℕ => p.1*p.2) (pair parameterStepsRealizer parameterProposalWidthRealizer) multiply)) multiply

theorem polynomial_parameterUnitWords : PolynomialTime parameterUnitWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_parameterTrials
    (polynomial_composition (polynomial_pair polynomial_parameterSteps polynomial_parameterProposalWidth)
      polynomial_multiply)) polynomial_multiply

attribute [local irreducible] parameterUnitWords

abbrev SamplingWordInput := SamplingParameters×List Bool

def unitSamplingBits (z : SamplingWordInput) : List Bool :=
  z.2.take (parameterUnitWords z.1)
def unitSamplingBitsRealizer : Realizer unitSamplingBits :=
  composition (f := fun z : SamplingWordInput => (z.2,parameterUnitWords z.1))
    (g := fun z : List Bool×ℕ => z.1.take z.2)
    (pair (f := fun z : SamplingWordInput => z.2)
      (g := fun z : SamplingWordInput => parameterUnitWords z.1) second
      (composition (f := fun z : SamplingWordInput => z.1)
        (g := parameterUnitWords) first parameterUnitWordsRealizer)) takeFast

theorem polynomial_unitSamplingBits : PolynomialTime unitSamplingBitsRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_parameterUnitWords)) polynomial_takeFast

def unitSamplingInput (z : SamplingWordInput) : ProfileRetryData :=
  (samplingRetryParameters z.1,unitSamplingBits z)
def unitSamplingInputRealizer : Realizer unitSamplingInput :=
  pair (composition (f := fun z : SamplingWordInput => z.1) (g := samplingRetryParameters)
    first samplingRetryParametersRealizer) unitSamplingBitsRealizer

theorem polynomial_unitSamplingInput : PolynomialTime unitSamplingInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_samplingRetryParameters)
    polynomial_unitSamplingBits

def unitSamplingMatrix (z : SamplingWordInput) : MatrixCode := unitProfileRetry (unitSamplingInput z)
def unitSamplingMatrixRealizer : Realizer unitSamplingMatrix :=
  composition (f := unitSamplingInput) (g := unitProfileRetry)
    unitSamplingInputRealizer unitProfileRetryRealizer

theorem polynomial_unitSamplingMatrix : PolynomialTime unitSamplingMatrixRealizer :=
  polynomial_composition polynomial_unitSamplingInput polynomial_unitProfileRetry

def parameterLargeIndices (row : Bool) (z : SamplingParameters) : List ℕ :=
  largeIndices (marginThreshold z.1,if row then z.1.1 else z.1.2)
def parameterLargeIndicesRealizer (row : Bool) : Realizer (parameterLargeIndices row) := by
  cases row with
  | false =>
    exact composition
      (f := fun z : SamplingParameters => (marginThreshold z.1,z.1.2)) (g := largeIndices)
      (pair (composition (f := fun z : SamplingParameters => z.1) (g := marginThreshold)
        first marginThresholdRealizer) (composition first second)) largeIndicesRealizer
  | true =>
    exact composition
      (f := fun z : SamplingParameters => (marginThreshold z.1,z.1.1)) (g := largeIndices)
      (pair (composition (f := fun z : SamplingParameters => z.1) (g := marginThreshold)
        first marginThresholdRealizer) (composition first first)) largeIndicesRealizer

theorem polynomial_parameterLargeIndices (row : Bool) : PolynomialTime (parameterLargeIndicesRealizer row) := by
  cases row with
  | false => exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginThreshold)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_largeIndices
  | true => exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginThreshold)
      (polynomial_composition polynomial_first polynomial_first)) polynomial_largeIndices

def hasLargeRectangle (z : SamplingParameters) : Bool :=
  decide (0<(parameterLargeIndices true z).length) && decide (0<(parameterLargeIndices false z).length)
def hasLargeRectangleRealizer : Realizer hasLargeRectangle :=
  composition (f := fun z : SamplingParameters =>
      (decide (0<(parameterLargeIndices true z).length),decide (0<(parameterLargeIndices false z).length)))
    (g := fun p : Bool×Bool => p.1 && p.2)
    (pair
      (composition (f := fun z : SamplingParameters => (0,(parameterLargeIndices true z).length))
        (g := fun p : ℕ×ℕ => decide (p.1<p.2))
        (pair (constant 0) (composition (f := parameterLargeIndices true) (g := List.length)
          (parameterLargeIndicesRealizer true) listLength)) less)
      (composition (f := fun z : SamplingParameters => (0,(parameterLargeIndices false z).length))
        (g := fun p : ℕ×ℕ => decide (p.1<p.2))
        (pair (constant 0) (composition (f := parameterLargeIndices false) (g := List.length)
          (parameterLargeIndicesRealizer false) listLength)) less)) boolAnd

theorem polynomial_hasLargeRectangle : PolynomialTime hasLargeRectangleRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition (polynomial_parameterLargeIndices true) polynomial_listLength)) polynomial_less)
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition (polynomial_parameterLargeIndices false) polynomial_listLength)) polynomial_less))
    polynomial_boolAnd

def samplingMatrixAll (z : SamplingParameters×List Bool) : MatrixCode :=
  if hasLargeRectangle z.1 then samplingMatrix z else unitSamplingMatrix z
def samplingMatrixAllRealizer : Realizer samplingMatrixAll :=
  choose (composition (f := fun z : SamplingParameters×List Bool => z.1) (g := hasLargeRectangle)
    first hasLargeRectangleRealizer) samplingMatrixRealizer unitSamplingMatrixRealizer

theorem polynomial_samplingMatrixAll : PolynomialTime samplingMatrixAllRealizer :=
  polynomial_choose (polynomial_composition polynomial_first polynomial_hasLargeRectangle)
    polynomial_samplingMatrix polynomial_unitSamplingMatrix

def publicSamplingAll (z : List MatchingFPRAS.Symbol×List Bool) : List MatchingFPRAS.Symbol :=
  GreedyFeasibleTable.printMatrix (samplingMatrixAll (parsedSampling z.1,z.2))
def publicSamplingAllRealizer : Realizer publicSamplingAll :=
  composition (f := fun z : List MatchingFPRAS.Symbol×List Bool =>
      samplingMatrixAll (parsedSampling z.1,z.2)) (g := GreedyFeasibleTable.printMatrix)
    (composition (f := fun z : List MatchingFPRAS.Symbol×List Bool => (parsedSampling z.1,z.2))
      (g := samplingMatrixAll) (pair (composition (f := fun z : List MatchingFPRAS.Symbol×List Bool => z.1)
        (g := parsedSampling) first parsedSamplingRealizer) second) samplingMatrixAllRealizer)
      GreedyFeasibleTable.printMatrixRealizer

theorem polynomial_publicSamplingAll : PolynomialTime publicSamplingAllRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_parsedSampling) polynomial_second)
    polynomial_samplingMatrixAll) GreedyFeasibleTable.polynomial_printMatrix

end ContingencyTables.ProfilePrograms

end OAI
