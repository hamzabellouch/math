import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential
import OAI.Geometry.SurfaceImmersion.Geometry.RestoredMetricTensor

namespace OAI

/-! Exact globalization of the actual metric linearization. The local
base map is the constructed smooth representative of the global map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4

lemma euclidean_linearized_coordinate_value (F U : SmallModes.Base → Space)
    {y : SmallModes.Base} (hF : DifferentiableAt ℝ F y) (hU : DifferentiableAt ℝ U y)
    (v w : SmallModes.Base) :
    PhaseMean.evaluate (RealModes.realLinearizedTensor (spaceCoordinates ∘ F) (spaceCoordinates ∘ U) y) v w =
      inner ℝ (fderiv ℝ F y v) (fderiv ℝ U y w) +
        inner ℝ (fderiv ℝ U y v) (fderiv ℝ F y w) := by
  rw [RealModes.evaluate_realLinearizedTensor]
  simp only [RealModes.realLinearized,SmallModes.coordDeriv]
  rw [(spaceCoordinates.hasFDerivAt.comp y hF.hasFDerivAt).fderiv,
    (spaceCoordinates.hasFDerivAt.comp y hU.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change spaceCoordinates (fderiv ℝ F y v) ⬝ᵥ spaceCoordinates (fderiv ℝ U y w) +
    spaceCoordinates (fderiv ℝ F y w) ⬝ᵥ spaceCoordinates (fderiv ℝ U y v) = _
  rw [spaceCoordinates_dot,spaceCoordinates_dot]
  congr 1
  exact real_inner_comm _ _

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
local instance restoredLinearFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredLinearFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredLinearDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredLinearDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredLinearSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredLinearSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem restored_linearized_metric (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (f : SmallModes.Base → Space)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (spaceCoordinates ∘ f) (planeCoordinateIsometry y))) := by
  funext p
  ext v w
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [linearMetricTensor_apply,A.tensorRestore_apply i _ hp,fiberFromThree_apply]
    have hd := A.plane_chart_differential i hp
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w) = _ at hw
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    change planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
      (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
      (surfaceDifferential (chart (i : M)) p w) = _ at hw
    rw [euclidean_linearized_coordinate_value _ _
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _) (hf.differentiable (by simp) _)]
    have hu := A.restore_plane_mfderiv i f hsp hp (hf.differentiable (by simp) _)
    change surfaceDifferential (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p =
      (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
        (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (surfaceDifferential (chart (i : M)) p)) at hu
    unfold linearMetricForm
    rw [hu]
    by_cases hs : p ∈ tsupport (A.weight i)
    · rw [A.vectorPlaneRead_differential i hF hs,A.outer_one i p hs,one_mul]
      simp only [ContinuousLinearMap.comp_apply,hv,hw]
      rfl
    · have hn : planeCoordinateIsometry (chart (i : M) p) ∉ tsupport f := by
        intro hh
        exact hs (A.mem_weight_support_of_plane i hp (hsp hh))
      rw [fderiv_of_notMem_tsupport ℝ hn]
      simp only [ContinuousLinearMap.zero_comp,zero_apply,inner_zero_left,inner_zero_right,add_zero,mul_zero]
  · have hs : p ∉ tsupport (A.weight i) := fun h => hp (A.weight_support i h)
    have hu := surfaceDifferential_zero_off_support
      (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))
      (fun h => hs (A.restore_plane_tsupport i f hsp h))
    have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [linearMetricTensor_apply,linearMetricForm,hu,zero_apply,inner_zero_left,
      inner_zero_right,add_zero,bundleRestore,ho,zero_smul]

end SmoothingAtlas
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
