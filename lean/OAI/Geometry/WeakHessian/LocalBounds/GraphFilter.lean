import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GraphReuse

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile174
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma filter_graph_tendsto_weakGradient (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {un An : ι → X → ℝ} {u A : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) l (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) l (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => (hn n).1.2.2.toLp (weakGradient m (un n))) l
      (𝓝 (hu.1.2.2.toLp (weakGradient m u))) := by

  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro r hr
  exact graph_tendsto_weakGradient hfinite hpar (fun n => hn (r n)) hu (ht.comp hr) (hAt.comp hr)

end WeakHessian

end
end InlinedFile174

end OAI
