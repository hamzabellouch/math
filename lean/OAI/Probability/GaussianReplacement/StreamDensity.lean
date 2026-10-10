import OAI.Probability.GaussianReplacement.StreamGram
import OAI.Probability.GaussianRegression.Projection

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace NoiselessRegression
open InnerProductSpace

section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ReplicaKernel

section GaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianKernel

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ProductDensity

section GaussianNoise

end GaussianNoise

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

end LimitSet

section OuterBound
variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

end OuterBound

section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionCoupling

end NoiselessRegression

end

end OAI
