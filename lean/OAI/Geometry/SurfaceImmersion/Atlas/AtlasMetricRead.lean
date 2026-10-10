import OAI.Geometry.SurfaceImmersion.Atlas.MetricChartReconstruction
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! On the active chart locus the local metric is exactly the chart read
of the induced global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance metricReadExactFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadExactFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricReadExactDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricReadExactDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricReadExactSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadExactSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma metric_component_on_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ tsupport (A.weight i)) :
    A.bundleComponent A.tensorTriv i (inducedTensor F) p =
      fiberFromThree (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) := by
  have hsource := A.weight_support i hp
  let f : Base → TensorFiber := fun y => fiberFromThree
    (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry y))
  have he : A.bundleRestore A.tensorTriv i f p = inducedTensor F p := by
    ext v w
    rw [A.tensorRestore_apply i f hsource,A.outer_one i p hp,one_mul]
    change fiberFromThree
      (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
        inducedForm F p v w
    rw [fiberFromThree_apply]
    have hd := A.vectorPlaneRead_differential i hF hp
    rw [A.plane_chart_differential i hsource] at hd
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [euclidean_metric_coordinate_value (A.vectorPlaneRead i F)
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _)]
    exact congrArg₂ (inner ℝ) hv.symm hw.symm
  have hc := congrArg ((A.tensorTriv i).continuousLinearMapAt ℝ p) he
  simp only [bundleRestore,A.outer_one i p hp,one_smul,
    (A.tensorTriv i).continuousLinearMapAt_symmL (A.tensorTriv_domain i hsource)] at hc
  exact hc.symm

lemma metric_read_on_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : Base}
    (hx : A.chartWeight i x ≠ 0) :
    RealModes.realMetricTensor (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry x) = A.tensorChartRead i (inducedTensor F) x := by
  have hxt : x ∈ (chart (i : M)).target := by
    by_contra hn
    exact hx (by simp only [chartWeight,indicator_of_notMem hn])
  have hw : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hxt] using hx
  have hp := subset_tsupport (A.weight i) hw
  have hread := A.tensorChartRead_on_weight i (inducedTensor F) hp
  rw [(chart (i : M)).right_inv hxt,A.metric_component_on_weight i hF hp,
    fiberToThree_fromThree,(chart (i : M)).right_inv hxt] at hread
  exact hread.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
