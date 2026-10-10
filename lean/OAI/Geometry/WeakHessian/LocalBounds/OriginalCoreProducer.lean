import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactOriginalCore
import OAI.Geometry.WeakHessian.LocalBounds.GraphReuse

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile178
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.originalTestGraphCore {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) : OriginalTestGraphCore m := by
  intro u A hu
  obtain ⟨gs,hgs,hgsc,us,As,hge,hAe,hut,hAt⟩ :=
    hrcd.original_compact_test_graph_approx hN hfull hfin o
      (hu.congr_ae hu.1.1.coeFn_toLp.symm hu.2.1.coeFn_toLp.symm)
  have eu (n : ℕ) : (laplacian_isLaplacian (hgs n).1).1.1.toLp (gs n) = us n := by
    apply Lp.ext
    exact (laplacian_isLaplacian (hgs n).1).1.1.coeFn_toLp.trans (hge n)
  have eA (n : ℕ) : (laplacian_isLaplacian (hgs n).1).2.1.toLp (laplacian m (gs n)) = As n := by
    apply Lp.ext
    exact (laplacian_isLaplacian (hgs n).1).2.1.coeFn_toLp.trans (hAe n)
  exact ⟨gs,hgs,hgsc,by simpa only [eu] using hut,by simpa only [eA] using hAt⟩
end WeakHessian

end
end InlinedFile178

end OAI
