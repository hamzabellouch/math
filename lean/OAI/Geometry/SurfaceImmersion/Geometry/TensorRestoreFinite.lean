import OAI.Geometry.SurfaceImmersion.Geometry.TensorPlaneReconstruction

namespace OAI

/-! Finite-sum linearity of the actual tensor restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial

local instance tensorRestoreFiniteFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorRestoreFiniteFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance tensorRestoreFiniteDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance tensorRestoreFiniteDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance tensorRestoreFiniteSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorRestoreFiniteSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorPlaneRestoreLM : (A.centers → SmallModes.Base → PhaseMean.Tensor) →ₗ[ℝ]
    ((p : M) → CovariantTwoTensor p) where
  toFun := A.tensorPlaneRestore
  map_add' := A.tensorPlaneRestore_add
  map_smul' := A.tensorPlaneRestore_smul

omit [CompactSpace M] in
lemma tensorPlaneRestore_sum {ι : Type*} [Fintype ι]
    (f : ι → A.centers → SmallModes.Base → PhaseMean.Tensor) :
    A.tensorPlaneRestore (∑ j, f j) = ∑ j, A.tensorPlaneRestore (f j) :=
  map_sum A.tensorPlaneRestoreLM f Finset.univ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
