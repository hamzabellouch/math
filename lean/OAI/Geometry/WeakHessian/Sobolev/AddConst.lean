import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.Minimal
import OAI.Geometry.WeakHessian.Sobolev.CongrAeLeft

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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
open scoped Topology
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma IsLocalWeakUpperGradient.add_const {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (c : ℝ) :
    IsLocalWeakUpperGradient m (fun x => f x+c) D := by
  refine ⟨hD.1,hD.2.1,fun π hπ hb => ?_⟩
  simpa only [add_sub_add_right_eq_sub] using hD.2.2 π hπ hb

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.add_const {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) (c : ℝ) :
    IsMinimalLocalWeakUpperGradient m (fun x => f x+c) D := by
  refine ⟨hD.1.add_const c,fun E hE => hD.2 E ?_⟩
  simpa only [add_neg_cancel_right] using hE.add_const (-c)

omit [BorelSpace X] in
lemma weakGradient_add_const_of_exists {f : X → ℝ}
    (hf : ∃ D, IsMinimalLocalWeakUpperGradient m f D) (c : ℝ) :
    weakGradient m (fun x => f x+c) =ᵐ[m] weakGradient m f :=
  weakGradient_ae_eq_of_isMinimal ((weakGradient_isMinimal hf).add_const c)

omit [BorelSpace X] in
lemma LocalSobolev.add_const (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) (c : ℝ) :
    LocalSobolev m (fun x => f x+c) := by
  refine ⟨fun o R hR => ?_,⟨_,(weakGradient_isMinimal hf.2).add_const c⟩⟩
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite _ Metric.isBounded_ball⟩
  exact (hf.1 o R hR).add (memLp_const c)

omit [BorelSpace X] in
lemma Sobolev.add_const [IsFiniteMeasure m] {f : X → ℝ}
    (hf : Sobolev m f) (c : ℝ) : Sobolev m (fun x => f x+c) :=
  ⟨hf.1.add (memLp_const c),hf.2.1.add_const (fun B _ => measure_lt_top m B) c,
    hf.2.2.ae_eq (weakGradient_add_const_of_exists hf.2.1.2 c).symm⟩

lemma Sobolev.normalContraction [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (hfinite : FiniteOnBoundedSets m) {f : X → ℝ} (hf : Sobolev m f)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) :
    Sobolev m (η ∘ f) :=
  Sobolev.of_upperGradient hfinite (hη.comp_memLp hη0 hf.1)
    (IsLocalWeakUpperGradient.normalContraction (weakGradient_isMinimal hf.2.1.2).1 hη)
    hf.2.2

end WeakHessian

end

end OAI
