import OAI.Geometry.SurfaceImmersion.Geometry.RestoredMetricTensor

namespace OAI

/-! Real-coordinate version of the supported metric restoration identity. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance realRestoredMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance realRestoredMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance realRestoredMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance realRestoredMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance realRestoredMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance realRestoredMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma real_restored_metric (i : A.centers) (f : SmallModes.Base → RealModes.RVec 4)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y =>
        fiberFromThree (RealModes.realMetricTensor f (planeCoordinateIsometry y))) := by
  have hrest := A.restored_metric_tensor i (spaceCoordinates.symm ∘ f)
    (spaceCoordinates.symm.contDiff.comp hf)
    ((tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) f).trans hsp)
  have he : restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ f) ∘ planeCoordinateIsometry) =
      spaceCoordinates.symm ∘ restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source <;>
      simp [restore,hp,Function.comp_apply,map_smul]
  have hcoord : spaceCoordinates ∘ (spaceCoordinates.symm ∘ f) = f := by
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [he,hcoord] at hrest
  exact hrest

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
