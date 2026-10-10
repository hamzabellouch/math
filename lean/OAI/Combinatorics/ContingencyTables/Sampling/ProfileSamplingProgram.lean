import OAI.Combinatorics.ContingencyTables.Sampling.ProfileScheduleProgram

namespace OAI

/-! # Preparing and executing the complete profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

/-- All constant configuration data is computed from the public margins. -/
def initialConfiguration (z : SamplingParameters) : ProfileConfiguration :=
  (((initialCheck z.1,marginPadding z.1),(parameterDimension z,parameterAccuracy z)),
    initialViews z.1)

def initialConfigurationRealizer : Realizer initialConfiguration :=
  pair (pair (pair (composition (f := fun z : SamplingParameters => z.1) (g := initialCheck) first initialCheckRealizer)
    (composition (f := fun z : SamplingParameters => z.1) (g := marginPadding) first marginPaddingRealizer))
    (pair parameterDimensionRealizer parameterAccuracyRealizer))
    (composition (f := fun z : SamplingParameters => z.1) (g := initialViews) first initialViewsRealizer)

theorem polynomial_initialConfiguration : PolynomialTime initialConfigurationRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_initialCheck)
    (polynomial_composition polynomial_first polynomial_marginPadding))
    (polynomial_pair polynomial_parameterDimension polynomial_parameterAccuracy))
    (polynomial_composition polynomial_first polynomial_initialViews)

def samplingSchedule (z : SamplingParameters) : ProfileWordSchedule :=
  ((parameterSteps z,parameterProposalWidth z),parameterCompletionWidth z)

def samplingScheduleRealizer : Realizer samplingSchedule :=
  pair (pair parameterStepsRealizer parameterProposalWidthRealizer) parameterCompletionWidthRealizer

theorem polynomial_samplingSchedule : PolynomialTime samplingScheduleRealizer :=
  polynomial_pair (polynomial_pair polynomial_parameterSteps polynomial_parameterProposalWidth)
    polynomial_parameterCompletionWidth

def samplingRetryParameters (z : SamplingParameters) : ProfileRetryParameters :=
  ((initialConfiguration z,samplingSchedule z),GreedyFeasibleTable.listMatrix z.1.1 z.1.2)

def samplingRetryParametersRealizer : Realizer samplingRetryParameters :=
  pair (pair initialConfigurationRealizer samplingScheduleRealizer)
    (composition (f := fun z : SamplingParameters => z.1) (g := fun z => GreedyFeasibleTable.listMatrix z.1 z.2) first GreedyFeasibleTable.tableRealizer)

theorem polynomial_samplingRetryParameters : PolynomialTime samplingRetryParametersRealizer :=
  polynomial_pair (polynomial_pair polynomial_initialConfiguration polynomial_samplingSchedule)
    (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table)

def samplingMatrix (z : SamplingParameters×List Bool) : MatrixCode :=
  profileRetry (samplingRetryParameters z.1,z.2)

def samplingMatrixRealizer : Realizer samplingMatrix :=
  composition (f := fun z : SamplingParameters×List Bool => (samplingRetryParameters z.1,z.2))
    (g := profileRetry)
    (pair (composition (f := fun z : SamplingParameters×List Bool => z.1)
      (g := samplingRetryParameters) first samplingRetryParametersRealizer) second) profileRetryRealizer

theorem polynomial_samplingMatrix : PolynomialTime samplingMatrixRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_samplingRetryParameters) polynomial_second)
    polynomial_profileRetry

end ContingencyTables.ProfilePrograms

end OAI
