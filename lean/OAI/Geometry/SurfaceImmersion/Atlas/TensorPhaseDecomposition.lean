import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.TensorFiberCoordinates
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry
import OAI.Geometry.Immersion.ClosedSurface.PhaseStock

namespace OAI

/-! The finite phase-basis decomposition on global symmetric tensor sections.
The atlas partition restores the tensor exactly, including chart overlaps. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)

local instance phaseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance phaseDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance phaseSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorEncode_symmetric {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ∀ p v w, u p v w = u p w v) :
    ∀ x i v w, A.tensorEncode u x i v w = A.tensorEncode u x i w v := by
  have ht : (fun p => tensorTranspose (u p)) = u := by
    funext p
    ext v w
    exact (hu p w v)
  intro x i v w
  have hh := A.tensorLocalize_flip i u
  rw [ht] at hh
  exact congrArg (fun b : TensorFiber => b v w) (congrFun hh x)

lemma tensorDecode_symmetric {f : Base → A.centers → TensorFiber}
    (hf : ∀ x i v w, f x i v w = f x i w v) :
    ∀ p v w, A.tensorDecode f p v w = A.tensorDecode f p w v := by
  have ht (i : A.centers) : (fun x => (f x i).flip) = (fun x => f x i) := by
    funext x
    ext v w
    exact hf x i w v
  intro p v w
  simp only [tensorDecode, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hh := A.tensorRestore_flip i (fun x => f x i)
  rw [ht] at hh
  exact congrArg (fun b : CovariantTwoTensor p => b v w) (congrFun hh p)

def phaseCoefficient (P : A.centers → PhaseBasis) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : Fin 3) (y : Base) : ℝ :=
  (P i).Q j (fiberToThree (A.tensorEncode u y i))

def phaseTensor (P : A.centers → PhaseBasis) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : Fin 3) : Base → TensorFiber :=
  fun y => A.phaseCoefficient P u i j y • fiberFromThree (covectorSquare ((P i).ξ j))

lemma sum_phaseTensor (P : A.centers → PhaseBasis) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ∀ p v w, u p v w = u p w v) (y : Base) (i : A.centers) :
    ∑ j : Fin 3, A.phaseTensor P u i j y = A.tensorEncode u y i := by
  change (∑ j : Fin 3, (P i).Q j (fiberToThree (A.tensorEncode u y i)) •
    fiberFromThree (covectorSquare ((P i).ξ j))) = _
  calc
    _ = ∑ j : Fin 3, fiberFromThree
        ((P i).Q j (fiberToThree (A.tensorEncode u y i)) • covectorSquare ((P i).ξ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (fiberFromThree.map_smul _ _).symm
    _ = fiberFromThree (∑ j : Fin 3,
        (P i).Q j (fiberToThree (A.tensorEncode u y i)) • covectorSquare ((P i).ξ j)) :=
      (map_sum fiberFromThree _ _).symm
    _ = _ := by
      rw [(P i).decomposition, fiberFromThree_toThree _ (A.tensorEncode_symmetric hu y i)]

/-- The actual finite restored phase family sums to the original global tensor. -/
theorem global_phase_tensor_decomposition (P : A.centers → PhaseBasis)
    {u : ∀ x : M, CovariantTwoTensor x} (hu : ∀ p v w, u p v w = u p w v) (p : M) :
    (∑ i : A.centers, ∑ j : Fin 3, A.bundleRestore A.tensorTriv i (A.phaseTensor P u i j) p) = u p := by
  have hi (i : A.centers) :
      (∑ j : Fin 3, A.bundleRestore A.tensorTriv i (A.phaseTensor P u i j) p) =
        A.bundleRestore A.tensorTriv i (fun y => A.tensorEncode u y i) p := by
    simp only [bundleRestore, ← Finset.smul_sum, ← map_sum]
    rw [A.sum_phaseTensor P hu]
  simp_rw [hi]
  exact congrFun (A.tensorDecode_encode u) p

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
