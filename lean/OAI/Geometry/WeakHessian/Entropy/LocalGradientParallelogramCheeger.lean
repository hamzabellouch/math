import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyMinimal
import OAI.Geometry.WeakHessian.Sobolev.SobolevCheegerEnergyTop
import OAI.Geometry.WeakHessian.Sobolev.MulBounded
import OAI.Geometry.WeakHessian.LocalBounds.Smul

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
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma localGradientParallelogram_of_cheeger [CompleteSpace X] [ProperSpace X] [Nonempty X]
    [TopologicalSpace.SeparableSpace X] {m : Measure X}
    (hfinite : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2)) :
    LocalGradientParallelogram m := by
  intro f g hf hg
  exact weakGradient_local_pointwise_parallelogram hfinite
    (fun _ _ hu hv => integral_parallelogram_of_cheeger hfinite h hID hu hv) hf hg

lemma CurvatureDimension.global_localGradientParallelogram [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
     {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) :
    LocalGradientParallelogram m := by
  let : Nonempty X := ⟨o⟩
  apply localGradientParallelogram_of_cheeger hfinite h
  intro f hf
  rw [hcd.global_cheegerEnergy_eq_weakGradient hfinite o hf,norm_toLp_sq_eq_integral]

lemma CurvatureDimension.global_generator_domain_reweight [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
     {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (u : X → ℝ) :
    (∃ A, IsLaplacian (exponentialMeasure m V) u A) ↔ ∃ A, IsLaplacian m u A :=
  inLaplacianDomain_exponentialMeasure_iff hfinite
    (hcd.global_localGradientParallelogram hfinite o h) hV hB u

lemma CurvatureDimension.global_generator_reweight [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
     {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    {u A V : X → ℝ} (hA : IsLaplacian m u A)
    {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) :
    IsLaplacian (exponentialMeasure m V) u (fun x => A x+gamma m V u x) :=
  hA.reweight hfinite (hcd.global_localGradientParallelogram hfinite o h) hV hB
end WeakHessian

end
end InlinedFile0

end OAI
