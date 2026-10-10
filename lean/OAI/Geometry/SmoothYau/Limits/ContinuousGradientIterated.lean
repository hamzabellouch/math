import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RealPhaseLinear

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
namespace YauCounterexamples
lemma continuous_gradient_of_iterated {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ1 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 1 (φ q.1) q.2)) :
    Continuous (fun p => gradient (φ p) 0) := by
  have he (p : X) : (continuousMultilinearCurryFin1 ℝ PhaseSpace ℝ)
      (iteratedFDeriv ℝ 1 (φ p) 0) = fderiv ℝ (φ p) 0 := by
    ext v
    exact iteratedFDeriv_one_apply (fun _ => v)
  unfold gradient
  exact (InnerProductSpace.toDual ℝ PhaseSpace).symm.continuous.comp (by
    simpa only [Function.comp_def,id_eq,he] using
      (continuousMultilinearCurryFin1 ℝ PhaseSpace ℝ).continuous.comp
        (hφ1.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))))
end YauCounterexamples

end

end OAI
