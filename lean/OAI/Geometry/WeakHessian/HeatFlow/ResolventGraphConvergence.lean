import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.BoundedSecondGenerator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile203
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.formGenerator_scaled_resolvent {u A : E}
    (hu : hQ.IsFormGenerator u A) {t : ℝ} (ht : 0 < t) :
    hQ.IsFormGenerator ((hQ.scale ht).resolventLinear u) ((hQ.scale ht).resolventLinear A) := by
  let R := (hQ.scale ht).resolventLinear
  let B := t⁻¹ • (R u-u)
  have hB : hQ.IsFormGenerator (R u) B := (hQ.scaled_resolvent_iff ht u _).mp rfl
  have hBB : hQ.IsFormGenerator B (t⁻¹ • (B-A)) :=
    hQ.formGenerator_smul _ (hQ.formGenerator_sub hB hu)
  have he : R A = B := (hQ.scaled_resolvent_iff ht A B).mpr hBB
  rwa [he]
end WeakHessianFunctional
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [IsLocallyFiniteMeasure m]

lemma cheeger_double_resolvent_graph_tendsto (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : ∀ i,0 < t i)
    (hl : Tendsto t l (𝓝 0)) :
    let R := fun i => ((cheeger_closedQuadraticEnergy h).scale (ht i)).resolventLinear
    (∀ i,(cheeger_closedQuadraticEnergy h).IsFormGenerator (R i (R i u)) (R i (R i A))) ∧
      Tendsto (fun i => R i (R i u)) l (𝓝 u) ∧ Tendsto (fun i => R i (R i A)) l (𝓝 A) := by
  refine ⟨fun i => ?_,cheeger_double_resolvent_tendsto h ht hl u,
    cheeger_double_resolvent_tendsto h ht hl A⟩
  exact (cheeger_closedQuadraticEnergy h).formGenerator_scaled_resolvent
    ((cheeger_closedQuadraticEnergy h).formGenerator_scaled_resolvent hu (ht i)) (ht i)
end WeakHessian

end
end InlinedFile203

end OAI
