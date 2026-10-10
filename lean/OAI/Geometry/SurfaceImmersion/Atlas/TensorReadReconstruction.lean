import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneWeight

namespace OAI

/-! Exact reconstruction from tensor readings and the squared atlas partition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base planeCoordinateIsometry)
local instance readReconstructFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance readReconstructFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance readReconstructDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance readReconstructDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance readReconstructSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance readReconstructSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorEncode_read_at (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x) (x : Base) :
    fiberToThree (A.tensorEncode u x i) =
      (A.chartWeight i x)^2 • A.tensorChartRead i u x := by
  by_cases hx : x ∈ (chart (i : M)).target
  · have hp : (chart (i : M)).symm x ∈ (chart (i : M)).source := (chart (i : M)).map_target hx
    have hh := A.tensorEncode_read i u hp
    simpa only [(chart (i : M)).right_inv hx,chartWeight,indicator_of_mem hx] using hh
  · simp only [tensorEncode,bundleLocalize,localize,indicator_of_notMem hx,
      map_zero,chartWeight,zero_pow (by decide : 2 ≠ 0),zero_smul]

lemma tensorPlaneRestore_partition_read (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ∀ p v w, u p v w = u p w v) :
    A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • A.tensorPlaneRead i u x) = u := by
  have heq (i : A.centers) (y : Base) :
      fiberFromThree ((A.chartWeight i y)^2 • A.tensorChartRead i u y) = A.tensorEncode u y i := by
    rw [← A.tensorEncode_read_at i u y]
    exact fiberFromThree_toThree _ (A.tensorEncode_symmetric hu y i)
  have hrestore : A.tensorPlaneRestore
      (fun i x => (A.planeWeight i x)^2 • A.tensorPlaneRead i u x) =
      A.tensorDecode (A.tensorEncode u) := by
    funext p
    apply Finset.sum_congr rfl
    intro i _
    have hf : (fun y => fiberFromThree ((A.planeWeight i (planeCoordinateIsometry y))^2 •
        A.tensorPlaneRead i u (planeCoordinateIsometry y))) = (fun y => A.tensorEncode u y i) := by
      funext y
      simpa only [planeWeight,tensorPlaneRead,Function.comp_apply,
        planeCoordinateIsometry.symm_apply_apply] using heq i y
    change A.bundleRestore A.tensorTriv i _ p = A.bundleRestore A.tensorTriv i _ p
    rw [hf]
  rw [hrestore,A.tensorDecode_encode]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
