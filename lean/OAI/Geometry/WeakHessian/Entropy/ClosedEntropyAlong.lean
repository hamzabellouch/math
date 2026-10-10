import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropyRealContinuousSupport

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u v
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma isClosed_entropy_le_along {T : Type v} [TopologicalSpace T]
    (μ : T → ProbabilityMeasure X) (hμ : Continuous μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hd : ∀ t, (μ t:Measure X) ≤ B • m)
    (a : T → ℝ) (ha : Continuous a) :
    IsClosed {t | entropyReal m (μ t:Measure X) ≤ a t} := by
  have he : {t | entropyReal m (μ t:Measure X) ≤ a t} =
      ⋂ g : X →ᵇ ℝ, {t | (∫ x, g x ∂(μ t:Measure X))-(∫ x, Real.exp (g x) ∂m)+1 ≤ a t} := by
    ext t
    simp only [mem_ofPred_eq,mem_iInter]
    have H := entropyReal_le_iff_continuous_support hB (hd t) (a := a t)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using H
  rw [he]
  apply isClosed_iInter
  intro g
  apply isClosed_le ?_ ha
  exact (((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp hμ).sub continuous_const).add continuous_const

end WeakHessian

end
end InlinedFile0

end OAI
