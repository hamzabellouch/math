import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ConstMul
import OAI.Geometry.WeakHessian.LocalBounds.ClosedQuadraticEnergy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheeger_closedQuadraticEnergy (h : QuadraticCheegerEnergy m) :
    ClosedQuadraticEnergy (fun f : Lp ℝ 2 m => cheegerEnergy m (f : X → ℝ)) := by
  refine ⟨lowerSemicontinuous_cheegerEnergy, ?_, ?_, ?_⟩
  · rw [cheegerEnergy_congr_ae (Lp.coeFn_zero ℝ 2 m)]
    exact cheegerEnergy_zero
  · intro c f
    rw [cheegerEnergy_congr_ae (Lp.coeFn_smul c f)]
    exact cheegerEnergy_const_mul c (f : X → ℝ)
  · intro f g hf hg
    rw [cheegerEnergy_congr_ae (Lp.coeFn_add f g), cheegerEnergy_congr_ae (Lp.coeFn_sub f g)]
    exact h (f : X → ℝ) (g : X → ℝ) hf hg

lemma existsUnique_cheeger_resolvent (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    ∃! f : Lp ℝ 2 m, ∀ g : Lp ℝ 2 m,
      cheegerEnergy m (f : X → ℝ) + ENNReal.ofReal (‖f-u‖^2/2) ≤
        cheegerEnergy m (g : X → ℝ) + ENNReal.ofReal (‖g-u‖^2/2) :=
  (cheeger_closedQuadraticEnergy h).existsUnique_minimizer u

end WeakHessian

end
end InlinedFile0

end OAI
