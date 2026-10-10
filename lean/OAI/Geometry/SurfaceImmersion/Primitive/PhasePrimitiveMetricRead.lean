import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSelfTensorRead
import OAI.Geometry.SurfaceImmersion.Geometry.InverseTensorPullback
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedTensorPullbackBound
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorTransition

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
local instance primitiveReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance primitiveReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_primitive (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (g h : SmoothMetric M) (χ : Base → ℝ) (a : SmallModes.Base → ℝ)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {p : Base} (hp : p ∈ e.target) (hactive : A.chartWeight i (e.symm p) ≠ 0) :
    A.phaseMetricRead i e.symm h (baseEquiv p) =
      A.phaseMetricRead i e.symm g (baseEquiv p) +
        χ (e.symm p) • ![(a (baseEquiv p))^2,0,0] := by
  have hx : e.symm p ∈ (chart (i : M)).target := by
    by_contra hn
    simp [chartWeight,hn] at hactive
  have hw : A.weight i ((chart (i : M)).symm (e.symm p)) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hx] using hactive
  have ho := A.outer_one i _ (subset_tsupport (A.weight i) hw)
  simp only [phaseMetricRead,baseEquiv.symm_apply_apply]
  rw [htarget,A.tensorChartRead_add,Pi.add_apply,map_add,
    A.tensorChartRead_restore_self i _ hx ho,localizedTensorPullback,map_smul,e.right_inv hp,
    tensorCoordinatePullback_inverse e he hi hp]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
