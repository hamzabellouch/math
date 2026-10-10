import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedEnergyClosure
import OAI.Geometry.WeakHessian.LocalBounds.GraphReuse

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile204
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_gamma_bounded_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A : X → ℝ}
    (hn : ∀ n,IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A)))
    {ξ : X → ℝ} (hξ : AEStronglyMeasurable ξ m) {B : ℝ} (hξb : ∀ᵐ x ∂m,|ξ x| ≤ B) :
    Tendsto (fun n => ∫ x,ξ x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x,ξ x*gamma m u u x ∂m)) := by
  have hD := graph_tendsto_weakGradient hfin hpar hn hu ht hAt
  have hval := tendsto_integral_bounded_Lp_sq hξ hξb hD
  have hid (v : X → ℝ) (hv : MemLp (weakGradient m v) 2 m) :
      (∫ x,ξ x*gamma m v v x ∂m) = ∫ x,ξ x*(hv.toLp (weakGradient m v) x)^2 ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) v,hv.coeFn_toLp] with x hΓ hx
    rw [hΓ,hx]
  simpa only [hid _ (hu.1.2.2),hid _ ((hn _).1.2.2)] using hval
end WeakHessian

end
end InlinedFile204

end OAI
