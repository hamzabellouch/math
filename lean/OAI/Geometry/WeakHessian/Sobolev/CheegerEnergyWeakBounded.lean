import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CongrAeLeft
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric

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
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsProbabilityMeasure m]

lemma CurvatureDimension.cheegerEnergy_le_weak_bounded {K N : ℝ}
    (hcd : CurvatureDimension m K N) (h : QuadraticCheegerEnergy m)
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hfb : ∀ᵐ x ∂m, |f x| ≤ B) :
    cheegerEnergy m (f : X → ℝ) ≤ ENNReal.ofReal (‖D‖^2/2) := by
  apply (cheeger_closedQuadraticEnergy h).energy_le_of_resolvent_pairing
    (cheeger_domain_dense h) f (norm_nonneg D)
  intro t ht
  apply hcd.weak_generator_pairing h
    (((cheeger_closedQuadraticEnergy h).scaled_resolvent_iff ht f _).mp rfl) hB
    (cheeger_scaled_resolvent_bounded h ht hB f hfb) hf

end WeakHessian
namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsProbabilityMeasure m]

lemma CurvatureDimension.cheegerEnergy_le_weak {K N : ℝ}
    (hcd : CurvatureDimension m K N) (h : QuadraticCheegerEnergy m)
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ)) :
    cheegerEnergy m (f : X → ℝ) ≤ ENNReal.ofReal (‖D‖^2/2) := by
  let fn : ℕ → Lp ℝ 2 m := fun n => (realClip_lipschitz n).compLp (realClip_zero n) f
  have hw (n : ℕ) : IsLocalWeakUpperGradient m (fn n : X → ℝ) (D : X → ℝ) :=
    (hf.normalContraction (realClip_lipschitz n)).congr_ae_left
      ((realClip_lipschitz n).coeFn_compLp (realClip_zero n) f).symm
  have hb (n : ℕ) : ∀ᵐ x ∂m, |fn n x| ≤ (n:ℝ) := by
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) f] with x hx
    rw [show fn n x = realClip n (f x) from hx]
    exact realClip_abs_le n (f x)
  exact ((cheeger_closedQuadraticEnergy h).lowerSemicontinuous.isClosed_preimage
    (ENNReal.ofReal (‖D‖^2/2))).mem_of_tendsto (realClip_tendsto_Lp f)
      (Eventually.of_forall fun n => hcd.cheegerEnergy_le_weak_bounded h (hw n)
        (Nat.cast_nonneg n) (hb n))

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

end
end
end InlinedFile0

end OAI
