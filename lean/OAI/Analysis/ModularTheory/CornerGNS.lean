import OAI.Analysis.ModularTheory.CompressedCorners
import OAI.Analysis.OperatorAlgebra.GNSHilbertStructure
import OAI.Analysis.PureInfiniteness.NormalizedCornerVector

namespace OAI

/-! The finite tracial GNS spaces embed isometrically in the actual modular
Hilbert space, with their vectors given by the concrete cutoff formula. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def modularCompressedTraceVector (S : StandardModularData H) (n : ℕ) :
    ModularCornerHilbert (H := H) (n + 1) :=
  ((‖modularCoreWeightVector S (n + 1)‖⁻¹ : ℝ) : ℂ) •
    (modularCornerInclusion (H := H) (n + 1)).toContinuousLinearMap.adjoint
      (modularCoreWeightVector S (n + 1))

lemma modularCompressedTracialState_vector (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S (n + 1)).toStarSubalgebra) :
    (modularCompressedTracialState S n).functional a =
      inner ℂ (modularCompressedTraceVector S n)
        ((a : ModularCornerHilbert (H := H) (n + 1) →L[ℂ]
          ModularCornerHilbert (H := H) (n + 1)) (modularCompressedTraceVector S n)) := by
  calc
    (modularCompressedTracialState S n).functional a =
        (modularCompressedTracialStateFormula S n).functional a :=
      congrArg (fun τ : Pureness.TracialState
        (modularCompressedCorner S (n + 1)).toStarSubalgebra => τ.functional a)
        (modularCompressedTracialState_eq S n)
    _ = _ := inner_normalized_corner (modularCornerInclusion (H := H) (n + 1))
      (modularCoreWeightVector S (n + 1)) a.val


attribute [local irreducible] modularCompressedTracialState

def modularCornerGNSInclusion (S : StandardModularData H) (n : ℕ) :
    gnsHilbert (modularCompressedTracialState S n).functional →ₗᵢ[ℂ]
      Lp H 2 (volume : Measure ℝ) :=
  normalizedCornerGNSInclusion (modularCornerInclusion (H := H) (n + 1))
    (modularCompressedTracialState S n).functional
    (modularCompressedCorner S (n + 1)).toStarSubalgebra.subtype
    (modularCoreWeightVector S (n + 1)) (modularCompressedTracialState_vector S n)

lemma modularCornerGNSInclusion_vector (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S (n + 1)).toStarSubalgebra) :
    modularCornerGNSInclusion S n
      ((modularCompressedTracialState S n).functional.toPreGNS a :
        (modularCompressedTracialState S n).functional.GNS) =
      ((‖modularCoreWeightVector S (n + 1)‖⁻¹ : ℝ) : ℂ) •
        isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val
          (modularCoreWeightVector S (n + 1)) :=
  normalizedCornerGNSInclusion_vector (modularCornerInclusion (H := H) (n + 1))
    (modularCompressedTracialState S n).functional
    (modularCompressedCorner S (n + 1)).toStarSubalgebra.subtype
    (modularCoreWeightVector S (n + 1)) (modularCompressedTracialState_vector S n) a

end WeakPureInfiniteness

end

end OAI
