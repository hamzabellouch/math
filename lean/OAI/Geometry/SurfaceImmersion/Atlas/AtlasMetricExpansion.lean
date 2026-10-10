import OAI.Geometry.SurfaceImmersion.Geometry.RestoredMetricTensor

namespace OAI

/-! The metric of the actual global oscillation, including every cross term
between different atlas patches. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance atlasMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def atlasMetricCross (f : A.centers → SmallModes.Base → Space) : ∀ p : M, CovariantTwoTensor p := by
  classical
  exact fun p => ∑ i : A.centers, ∑ j ∈ Finset.univ.erase i,
    metricPairTensor (restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry))
      (restore (j : M) (A.outer j) (f j ∘ planeCoordinateIsometry)) p

theorem vectorPlaneRestore_metric (f : A.centers → SmallModes.Base → Space)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realMetricTensor (spaceCoordinates ∘ f i)) +
        A.atlasMetricCross f := by
  classical
  unfold vectorPlaneRestore
  rw [inducedTensor_finite_sum (fun i : A.centers =>
    restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry)) (fun i => restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) ((hf i).comp planeCoordinateIsometry.contDiff))]
  apply congrArg₂ (·+·) _ rfl
  funext p
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.restored_metric_tensor i (f i) (hf i) (hsp i)) p

omit [CompactSpace M] in
lemma euclidean_vectorPlaneRestore (f : A.centers → SmallModes.Base → RealModes.RVec 4) :
    spaceCoordinates.symm ∘ A.vectorPlaneRestore f =
      A.vectorPlaneRestore (fun i => spaceCoordinates.symm ∘ f i) := by
  funext p
  simp only [vectorPlaneRestore,Function.comp_apply,Finset.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,map_smul]
  · simp only [restore,indicator_of_notMem hp,map_zero]

theorem euclidean_vectorPlaneRestore_metric
    (f : A.centers → SmallModes.Base → RealModes.RVec 4)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realMetricTensor (f i)) +
        A.atlasMetricCross (fun i => spaceCoordinates.symm ∘ f i) := by
  rw [A.euclidean_vectorPlaneRestore]
  have hh := A.vectorPlaneRestore_metric (fun i => spaceCoordinates.symm ∘ f i)
    (fun i => spaceCoordinates.symm.contDiff.comp (hf i))
    (fun i => (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) (f i)).trans (hsp i))
  have he (i : A.centers) : spaceCoordinates ∘ (spaceCoordinates.symm ∘ f i) = f i := by
    funext x
    simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  simpa only [he] using hh

lemma atlasMetricCross_pair_zero (f : A.centers → SmallModes.Base → Space)
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (i j : A.centers) {p : M} (hp : p ∉ tsupport (A.weight i) ∩ tsupport (A.weight j)) :
    metricPairTensor (restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry))
      (restore (j : M) (A.outer j) (f j ∘ planeCoordinateIsometry)) p = 0 := by
  apply metricPairTensor_zero_off_intersection
  intro h
  exact hp ⟨A.restore_plane_tsupport i (f i) (hsp i) h.1,
    A.restore_plane_tsupport j (f j) (hsp j) h.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
