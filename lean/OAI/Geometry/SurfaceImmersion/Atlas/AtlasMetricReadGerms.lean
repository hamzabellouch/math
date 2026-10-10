import OAI.Geometry.SurfaceImmersion.Atlas.AtlasReadGerms
import OAI.Geometry.SurfaceImmersion.Atlas.MetricAtlasReference

namespace OAI

/-! A metric atlas reading agrees as a germ with the actual coordinate
metric when the outer cutoff is locally one. This also identifies its
first derivative, as required by the connection estimates. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseMean
local instance metricReadGermFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadGermFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance metricReadGermDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricReadGermDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricReadGermSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadGermSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorPlaneRead_metric_outer_one (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source) (ho : A.outer i p = 1) :
    A.tensorPlaneRead i g.inner (coordinateChart (i : M) p) =
      coordinateMetric g (i : M) (coordinateChart (i : M) p) := by
  change A.tensorChartRead i g.inner
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) p))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  have hread : A.tensorChartRead i g.inner (chart (i : M) p) =
      fiberToThree (A.bundleComponent A.tensorTriv i g.inner p) := by
    change fiberToThree (localize (i : M) (A.outer i)
      (A.bundleComponent A.tensorTriv i g.inner) (chart (i : M) p)) = _
    rw [localize_chart _ _ _ hp,ho]
    simp only [one_pow,one_smul]
  rw [hread]
  ext k
  rw [fiberToThree_apply,A.tensorComponent_metric g i hp]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate,firstDirection,secondDirection,SmallModes.dx,SmallModes.dy]

lemma tensorPlaneRead_metric_germ (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    A.tensorPlaneRead i g.inner =ᶠ[𝓝 (coordinateChart (i : M) p)] coordinateMetric g (i : M) := by
  let e := coordinateChart (i : M)
  have hps : p ∈ e.source := by simpa only [e,coordinateChart_source,chart_source] using hp
  have hpt := e.map_source hps
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    have hc := (e.continuousOn_symm _ hpt).continuousAt (e.open_target.mem_nhds hpt)
    simpa only [e.left_inv hps] using hc.tendsto
  filter_upwards [e.open_target.mem_nhds hpt,ho.comp_tendsto ht] with y hy hoy
  have hq : e.symm y ∈ (chart (i : M)).source := by
    simpa only [e,coordinateChart_source,chart_source] using e.map_target hy
  have he := A.tensorPlaneRead_metric_outer_one g i hq hoy
  change A.tensorPlaneRead i g.inner (e (e.symm y)) = coordinateMetric g (i : M) (e (e.symm y)) at he
  simpa only [e.right_inv hy] using he

lemma tensorPlaneRead_metric_firstJet (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    (A.tensorPlaneRead i g.inner (coordinateChart (i : M) p),
      fderiv ℝ (A.tensorPlaneRead i g.inner) (coordinateChart (i : M) p)) =
    (coordinateMetric g (i : M) (coordinateChart (i : M) p),
      fderiv ℝ (coordinateMetric g (i : M)) (coordinateChart (i : M) p)) := by
  have he := A.tensorPlaneRead_metric_germ g i hp ho
  exact Prod.ext he.eq_of_nhds he.fderiv_eq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
