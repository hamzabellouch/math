import OAI.Analysis.OperatorAlgebra.HilbertProjectionRange
import OAI.Analysis.OperatorAlgebra.IsometricCornerExpectation
import OAI.Analysis.ModularTheory.FiniteStates

namespace OAI

/-! The concrete range-space representation of the finite modular corners. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ComplexOrder CStarAlgebra TensorProduct

namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ModularCornerHilbert (n : ℕ) :=
  HilbertProjectionRange (modularFiniteProjection (H := H) n)
    (modularFiniteProjection_isStarProjection n)

def modularCornerInclusion (n : ℕ) :
    ModularCornerHilbert (H := H) n →ₗᵢ[ℂ] Lp H 2 (volume : Measure ℝ) :=
  hilbertProjectionInclusion _ _

lemma modularCornerInclusion_projection (n : ℕ) :
    isometricCornerProjection (modularCornerInclusion (H := H) n) = modularFiniteProjection (H := H) n :=
  hilbertProjectionInclusion_projection _ _

lemma modularCornerProjection_mem (S : StandardModularData H) (n : ℕ) :
    isometricCornerProjection (modularCornerInclusion (H := H) n) ∈ modularCrossedProduct volume S := by
  rw [modularCornerInclusion_projection]
  exact modularFiniteProjection_mem S n

def modularCompressedCorner (S : StandardModularData H) (n : ℕ) :
    VonNeumannAlgebra (ModularCornerHilbert (H := H) n) :=
  isometricCornerVonNeumann (modularCrossedProduct volume S) (modularCornerInclusion (H := H) n)
    (modularCornerProjection_mem S n)

lemma modularCornerLift_mem (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S n).toStarSubalgebra) :
    isometricCornerLift (modularCornerInclusion (H := H) n) a ∈ modularCrossedProduct volume S :=
  (isometricCornerVonNeumann_mem_iff (modularCrossedProduct volume S)
    (modularCornerInclusion (H := H) n) (modularCornerProjection_mem S n) a.val).mp a.property

lemma modularCornerLift_left (n : ℕ)
    (a : ModularCornerHilbert (H := H) n →L[ℂ] ModularCornerHilbert (H := H) n) :
    modularFiniteProjection (H := H) n * isometricCornerLift (modularCornerInclusion (H := H) n) a =
      isometricCornerLift (modularCornerInclusion (H := H) n) a := by
  have he := congrArg (fun p : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) =>
    p * isometricCornerLift (modularCornerInclusion (H := H) n) a)
    (modularCornerInclusion_projection (H := H) n)
  apply he.symm.trans
  apply ContinuousLinearMap.ext
  intro x
  exact isometricCornerProjection_inclusion (modularCornerInclusion (H := H) n)
    (a ((modularCornerInclusion (H := H) n).toContinuousLinearMap.adjoint x))

lemma modularCornerLift_right (n : ℕ)
    (a : ModularCornerHilbert (H := H) n →L[ℂ] ModularCornerHilbert (H := H) n) :
    isometricCornerLift (modularCornerInclusion (H := H) n) a * modularFiniteProjection (H := H) n =
      isometricCornerLift (modularCornerInclusion (H := H) n) a := by
  have he := congrArg (fun p : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) =>
    isometricCornerLift (modularCornerInclusion (H := H) n) a * p)
    (modularCornerInclusion_projection (H := H) n)
  apply he.symm.trans
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, isometricCornerLift_apply, isometricCornerProjection_apply,
    isometricCorner_adjoint_apply]

def modularCornerLiftInCore (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S n).toStarSubalgebra) :
    (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra :=
  ⟨isometricCornerLift (modularCornerInclusion (H := H) n) a.val, modularCornerLift_mem S n a⟩

def modularCornerToAbstractFun (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S n).toStarSubalgebra) : ModularFiniteCorner S n := by
  refine ⟨modularCornerLiftInCore S n a, ?_, ?_⟩
  · apply Subtype.ext
    exact modularCornerLift_left n a.val
  · apply Subtype.ext
    exact modularCornerLift_right n a.val


end WeakPureInfiniteness

end

end OAI
