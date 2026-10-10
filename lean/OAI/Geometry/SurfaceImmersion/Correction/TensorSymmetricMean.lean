import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanIteration
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPhaseDecomposition

namespace OAI

/-! Symmetry is invariant under the actual global finite mean iteration. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle

local instance symmetricMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance symmetricMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance symmetricMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance symmetricMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance symmetricMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance symmetricMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorMeanTrial_symmetric (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x)
    (hH : ∀ p v w, H p v w = H p w v)
    (hT : ∀ u, (∀ p v w, u p v w = u p w v) → ∀ p v w, T u p v w = T u p w v)
    (j : ℕ) : ∀ p v w, A.tensorMeanTrial H T j p v w = A.tensorMeanTrial H T j p w v := by
  induction j with
  | zero => simpa only [A.tensorMeanTrial_zero] using hH
  | succ j ih =>
    rw [A.tensorMeanTrial_succ]
    intro p v w
    change H p v w - T (A.tensorMeanTrial H T j) p v w =
      H p w v - T (A.tensorMeanTrial H T j) p w v
    rw [hH p v w, hT _ ih p v w]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
