import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneCoordinates

namespace OAI

/-! Exact reconstruction from the three independent tensor coordinates. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean
open JetPolynomial (Base planeCoordinateIsometry)

local instance reconstructionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance reconstructionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance reconstructionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance reconstructionSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorPlaneEncode (u : ∀ x : M, CovariantTwoTensor x) (i : A.centers) : SmallModes.Base → Tensor :=
  fun y => fiberToThree (A.tensorEncode u (planeCoordinateIsometry.symm y) i)

lemma tensorPlaneRestore_encode (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ∀ p v w, u p v w = u p w v) : A.tensorPlaneRestore (A.tensorPlaneEncode u) = u := by
  have he : (fun x i => fiberFromThree (A.tensorPlaneEncode u i (planeCoordinateIsometry x))) =
      A.tensorEncode u := by
    funext x i
    simp only [tensorPlaneEncode, LinearIsometryEquiv.symm_apply_apply]
    exact fiberFromThree_toThree _ (A.tensorEncode_symmetric hu x i)
  change A.tensorDecode (fun x i => fiberFromThree (A.tensorPlaneEncode u i (planeCoordinateIsometry x))) = u
  rw [he, A.tensorDecode_encode]

lemma tensorPlaneRestore_add (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f+g) = A.tensorPlaneRestore f + A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.add_apply, map_add, bundleRestore, smul_add,
    Finset.sum_add_distrib]

lemma tensorPlaneRestore_smul (a : ℝ) (f : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (a • f) = a • A.tensorPlaneRestore f := by
  funext p
  simp only [tensorPlaneRestore, Pi.smul_apply, map_smul, bundleRestore, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
