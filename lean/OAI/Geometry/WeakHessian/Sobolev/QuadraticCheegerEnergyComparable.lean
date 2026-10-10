import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyMinimal
import OAI.Geometry.WeakHessian.Sobolev.SobolevCheegerEnergyTop

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
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X} [IsProbabilityMeasure m]

lemma CurvatureDimension.quadraticCheegerEnergy_comparable {K N : ℝ}
    (hcd : CurvatureDimension m K N) (h : QuadraticCheegerEnergy m)
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m) :
    QuadraticCheegerEnergy ν := by
  apply quadraticCheegerEnergy_of_comparable (fun B _ => measure_lt_top m B) h ?_ hm hν
  intro f hf
  rw [hcd.cheegerEnergy_eq_weakGradient h hf,norm_toLp_sq_eq_integral]
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

end
end
end InlinedFile0

end OAI
