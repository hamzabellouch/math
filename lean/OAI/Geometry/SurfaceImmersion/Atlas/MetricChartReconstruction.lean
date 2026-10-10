import OAI.Geometry.SurfaceImmersion.Correction.AtlasLinearizedMetric
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneWeight

namespace OAI

/-! Recover the actual global metric from unweighted chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance metricReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem metric_from_chart_reads {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    A.tensorPlaneRestore (fun i y => (A.planeWeight i y)^2 •
      RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y) = inducedTensor F := by
  funext p
  have he (i : A.centers) :
      A.bundleRestore A.tensorTriv i (fun y =>
        fiberFromThree ((A.planeWeight i (planeCoordinateIsometry y))^2 •
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
            (planeCoordinateIsometry y))) p = (A.weight i p)^2 • inducedTensor F p := by
    ext v w
    by_cases hp : p ∈ (chart (i : M)).source
    · rw [A.tensorRestore_apply i _ hp]
      have hwgt : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = A.weight i p := by
        simp only [planeWeight,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply,
          chartWeight,indicator_of_mem ((chart (i : M)).map_source hp),
          (chart (i : M)).left_inv hp]
      rw [hwgt,map_smul]
      change A.outer i p * ((A.weight i p)^2 * _) = (A.weight i p)^2 * _
      by_cases hw : A.weight i p = 0
      · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero]
      · have hsp := subset_tsupport (A.weight i) hw
        rw [A.outer_one i p hsp,one_mul]
        congr 1
        change fiberFromThree
          (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
            (planeCoordinateIsometry (chart (i : M) p)))
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
          inducedForm F p v w
        rw [fiberFromThree_apply]
        have hd := A.vectorPlaneRead_differential i hF hsp
        rw [A.plane_chart_differential i hp] at hd
        have hv := congrArg (fun L => L v) hd
        have hw' := congrArg (fun L => L w) hd
        simp only [ContinuousLinearMap.comp_apply] at hv hw'
        rw [euclidean_metric_coordinate_value (A.vectorPlaneRead i F)
          ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _)]
        exact congrArg₂ (inner ℝ) hv.symm hw'.symm
    · have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (A.outer_support i h))
      have hw : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (A.weight_support i h))
      simp only [bundleRestore,ho,hw,zero_pow (by decide : 2 ≠ 0),zero_smul,zero_apply]
  change (∑ i : A.centers, A.bundleRestore A.tensorTriv i _ p) = _
  simp_rw [he]
  rw [← Finset.sum_smul,A.partition,one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
