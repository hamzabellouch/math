import OAI.Probability.GaussianReplacement.StreamDensity
import OAI.Probability.GaussianRegression.Support

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace NoiselessRegression
open InnerProductSpace

section SupportVolume
open scoped Pointwise

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end NetNorm

section SupportExistence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SupportExistence

end SupportVolume

end NoiselessRegression

end

end OAI
