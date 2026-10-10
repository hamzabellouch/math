import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneCoordinates

namespace OAI

/-! The fixed atlas estimate for the single tensor patch of a primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
local instance singleTensorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance singleTensorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance singleTensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance singleTensorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance singleTensorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance singleTensorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
local instance singleTensorCentersDecidableEq : DecidableEq A.centers := Classical.decEq _

omit [CompactSpace M] in
lemma tensorPlaneRestore_single (i : A.centers) (f : SmallModes.Base → PhaseMean.Tensor) :
    A.tensorPlaneRestore (fun j => if j = i then f else 0) =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f (planeCoordinateIsometry y))) := by
  classical
  funext p
  unfold tensorPlaneRestore
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji,bundleRestore]
  · exact fun hi => False.elim (hi (Finset.mem_univ _))

lemma single_tensor_restore_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : SmallModes.Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ s m C f →
      A.TensorWeightedBound s m (D*C)
        (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f (planeCoordinateIsometry y)))) := by
  classical
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [← A.tensorPlaneRestore_single i f]
  apply hd _ s C hs hs1 hC
  · intro j
    split_ifs
    · exact hf
    · exact contDiff_const
  · intro j
    split_ifs
    · exact hb
    · exact (weightedBound_zero univ s m).mono_const hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
