import OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricTensor

namespace OAI

/-! Restoring a compactly supported Euclidean displacement restores its
actual metric tensor, with no extra terms from the outer atlas cutoff. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance restoredMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma plane_chart_differential (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (surfaceDifferential (chart (i : M)) p) =
      planeCoordinates.toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) ∘ chart (i : M) =
      coordinateChart (i : M) := by
    funext x
    rfl
  have hd := mfderiv_comp p
    ((planeCoordinateIsometry.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp))
  rw [he, mfderiv_eq_fderiv] at hd
  change surfaceDifferential (coordinateChart (i : M)) p =
    (fderiv ℝ planeCoordinateIsometry (chart (i : M) p)).comp
      (surfaceDifferential (chart (i : M)) p) at hd
  have hi : fderiv ℝ (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base)
      (chart (i : M) p) = planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap :=
    planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [hi] at hd
  exact hd.symm.trans (A.coordinateChart_tangentCoordinates i hp)

lemma restored_metric_tensor (i : A.centers) (f : SmallModes.Base → Space)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y =>
        fiberFromThree (RealModes.realMetricTensor (spaceCoordinates ∘ f) (planeCoordinateIsometry y))) := by
  funext p
  ext v w
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [inducedTensor_apply, A.restore_plane_metric_on_source i f hsp hp
      (hf.differentiable (by simp) _), A.tensorRestore_apply i _ hp,
      fiberFromThree_apply]
    have hd := A.plane_chart_differential i hp
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w) = _ at hw
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [hv,hw]
    by_cases hs : p ∈ tsupport (A.weight i)
    · rw [A.outer_one i p hs,one_mul]
      rfl
    · have hn : planeCoordinateIsometry (chart (i : M) p) ∉ tsupport f := by
        intro hh
        exact hs (A.mem_weight_support_of_plane i hp (hsp hh))
      simp only [euclidean_metric_coordinate_value f (hf.differentiable (by simp) _),
        fderiv_of_notMem_tsupport ℝ hn,zero_apply,inner_zero_right,mul_zero]
  · have hs : p ∉ tsupport (A.weight i) := fun h => hp (A.weight_support i h)
    rw [inducedTensor_apply, A.restore_plane_metric_off_support i f hsp hs]
    have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [bundleRestore,ho,zero_smul,zero_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
