import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanCoordinates
import OAI.Geometry.SurfaceImmersion.Correction.FixedMeanSubstitution

namespace OAI

/-! Finite mean substitution on actual global tensor sections, represented
by redundant atlas coordinates. Every iterate stays in the representation
range, so no leading-identity premise on arbitrary plane fields is needed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance iterationModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance iterationModelSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance iterationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance iterationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

local instance iterationSectionTensorNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance iterationSectionTensorSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorEncodeLM : (∀ x : M, CovariantTwoTensor x) →ₗ[ℝ] (Base → A.centers → TensorFiber) where
  toFun := A.tensorEncode
  map_add' := A.tensorEncode_add
  map_smul' := A.tensorEncode_smul

def tensorDecodeLM : (Base → A.centers → TensorFiber) →ₗ[ℝ] (∀ x : M, CovariantTwoTensor x) where
  toFun := A.tensorDecode
  map_add' := A.tensorDecode_add
  map_smul' := A.tensorDecode_smul

def tensorProjectLM : (Base → A.centers → TensorFiber) →ₗ[ℝ] (Base → A.centers → TensorFiber) :=
  A.tensorEncodeLM.comp A.tensorDecodeLM

def tensorMeanOperator
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x)
    (f : Base → A.centers → TensorFiber) : Base → A.centers → TensorFiber :=
  A.tensorEncode (T (A.tensorDecode f))

lemma tensorMeanOperator_project
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x)
    (f : Base → A.centers → TensorFiber) :
    A.tensorProjectLM (A.tensorMeanOperator T f) = A.tensorMeanOperator T f :=
  A.tensorProject_encode _

lemma tensorMean_trial_project (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorProjectLM (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j) =
      fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j := by
  induction j with
  | zero => exact A.tensorProject_encode H
  | succ j _ =>
    change A.tensorProjectLM (A.tensorEncode H - A.tensorMeanOperator T
      (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)) = _
    rw [(A.tensorProjectLM).map_sub,show A.tensorProjectLM (A.tensorEncode H) = A.tensorEncode H from
      A.tensorProject_encode H,A.tensorMeanOperator_project]
    rfl

def tensorMeanTrial (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    ∀ x : M, CovariantTwoTensor x :=
  A.tensorDecode (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)

lemma tensorEncode_meanTrial (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorEncode (A.tensorMeanTrial H T j) =
      fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j :=
  A.tensorMean_trial_project H T j

lemma tensorMeanTrial_zero (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) :
    A.tensorMeanTrial H T 0 = H := A.tensorDecode_encode H

lemma tensorMeanTrial_succ (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorMeanTrial H T (j + 1) = H - T (A.tensorMeanTrial H T j) := by
  change A.tensorDecode (A.tensorEncode H - A.tensorMeanOperator T
    (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)) = _
  rw [A.tensorDecode_sub, A.tensorDecode_encode]
  change H - A.tensorDecode (A.tensorEncode (T (A.tensorMeanTrial H T j))) = _
  rw [A.tensorDecode_encode]

lemma tensorEncode_meanResidual (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorEncode (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H) =
      fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j +
        A.tensorMeanOperator T (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j) -
        A.tensorEncode H := by
  rw [A.tensorEncode_sub, A.tensorEncode_add, A.tensorEncode_meanTrial]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
