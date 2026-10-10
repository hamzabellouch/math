import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceOperatorStability
import OAI.Geometry.SurfaceImmersion.Atlas.InducedMetricReadTolerance

namespace OAI

/-! The actual remainder metric inherits the fixed positive inverse margins
from C1 approximation of the reference immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance refMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance refMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance refMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance refMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensor_frame_read (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ∀ p v w, u p v w = u p w v) {p : M} (hp : p ∈ tsupport (B.weight i)) :
    (B.tensorTriv i).continuousLinearMapAt ℝ p (u p) =
      fiberFromThree (B.tensorChartRead i u (chart (i : M) p)) := by
  rw [B.tensorChartRead_on_weight i u hp]
  apply (fiberFromThree_toThree _ ?_).symm
  intro v w
  change B.bundleComponent B.tensorTriv i u p v w = B.bundleComponent B.tensorTriv i u p w v
  rw [B.tensorComponent_apply i u (B.weight_support i hp),
    B.tensorComponent_apply i u (B.weight_support i hp)]
  exact hu p _ _

end SmoothingAtlas
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem metric_frame_tolerance {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 eps (G-F) →
      ∀ i p, p ∈ tsupport (d.B.weight i) →
        ‖(d.B.tensorTriv i).continuousLinearMapAt ℝ p
          ((g.inner-inducedTensor (r • G)) p)-d.chartReference i (chart (i : M) p)‖ < eta := by
  obtain ⟨eps,heps,hnear⟩ := A.induced_metric_read_tolerance d.B hF r
    (div_pos heta (show 0 < ‖fiberFromThree‖+1 by positivity))
  refine ⟨eps,heps,?_⟩
  intro G hG hb i p hp
  have hsym : ∀ p v w, (g.inner-inducedTensor (r • G)) p v w =
      (g.inner-inducedTensor (r • G)) p w v := by
    intro p v w
    change g.inner p v w-inner ℝ (mfderiv planeModel spaceModel (r • G) p v)
      (mfderiv planeModel spaceModel (r • G) p w) =
      g.inner p w v-inner ℝ (mfderiv planeModel spaceModel (r • G) p w)
      (mfderiv planeModel spaceModel (r • G) p v)
    rw [g.symm,real_inner_comm]
  rw [d.B.tensor_frame_read i _ hsym hp]
  change ‖fiberFromThree (d.B.tensorChartRead i (g.inner-inducedTensor (r • G)) (chart (i : M) p))-
    fiberFromThree (d.B.tensorChartRead i gref.inner (chart (i : M) p))‖ < eta
  rw [← map_sub]
  have hread : d.B.tensorChartRead i (g.inner-inducedTensor (r • G)) (chart (i : M) p)-
      d.B.tensorChartRead i gref.inner (chart (i : M) p) =
      -d.B.tensorChartRead i (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p) := by
    rw [href]
    simp only [d.B.tensorChartRead_on_weight i _ hp, SmoothingAtlas.bundleComponent,
      Pi.sub_apply,map_sub]
    abel
  rw [hread,map_neg,norm_neg]
  have h := (fiberFromThree.le_opNorm
    (d.B.tensorChartRead i (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p)))
  have hn := hnear G hG hb i (chart (i : M) p)
  have hmul : ‖fiberFromThree‖ * ‖d.B.tensorChartRead i
      (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p)‖ < eta := by
    have he := (lt_div_iff₀ (show 0 < ‖fiberFromThree‖+1 by positivity)).mp hn
    nlinarith [norm_nonneg (d.B.tensorChartRead i
      (inducedTensor (r • G)-inducedTensor (r • F)) (chart (i : M) p))]
  exact h.trans_lt hmul

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
