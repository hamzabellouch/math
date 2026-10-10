import OAI.Geometry.SurfaceImmersion.Geometry.SingleTensorRestoreBound
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorLocalBounds

namespace OAI

/-! Bounds on an open neighborhood of the outer support suffice for the
single tensor patch in the primitive construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
local instance localSingleTensorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance localSingleTensorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance localSingleTensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance localSingleTensorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance localSingleTensorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance localSingleTensorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem single_tensor_restore_bound_on_outer (i : A.centers)
    {U : Set JetPolynomial.Base} (hU : IsOpen U)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ U) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : SmallModes.Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m C f →
      A.TensorWeightedBound s m (D*C)
        (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f (planeCoordinateIsometry y)))) := by
  classical
  let V : A.centers → Set JetPolynomial.Base := fun j => if j = i then U else univ
  have hV : ∀ j, IsOpen (V j) := by
    intro j
    by_cases hji : j = i <;> simp [V,hji,hU]
  have hout : ∀ j : A.centers, (chart (j : M)) '' tsupport (A.outer j) ⊆ V j := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [V,ite_true] using houter
    · simp only [V,ite_eq_right hji]
      exact subset_univ _
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound_on_outer V hV hout m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [← A.tensorPlaneRestore_single i f]
  apply hd _ (by intro j; split_ifs; exact hf; exact contDiff_const) s C hs hs1 hC
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [V,ite_true] using hb
  · simp only [ite_eq_right hji]
    exact (weightedBound_zero _ s m).mono_const hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
