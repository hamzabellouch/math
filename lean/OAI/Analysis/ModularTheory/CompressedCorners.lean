import OAI.Analysis.ModularTheory.CornerRepresentation
import OAI.Analysis.ModularTheory.FixedPointIdentification
import OAI.Analysis.OperatorAlgebra.TracialMinimalMultiplication
import OAI.Analysis.OperatorAlgebra.TracialStatePullback

namespace OAI

/-! Constructed traces, cpc retractions, and the resulting minimal tensor
bound for the finite modular corners. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ComplexOrder CStarAlgebra TensorProduct

namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularCornerToAbstract (S : StandardModularData H) (n : ℕ) :
    (modularCompressedCorner S n).toStarSubalgebra →⋆ₐ[ℂ] ModularFiniteCorner S n where
  toFun := modularCornerToAbstractFun S n
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    change isometricCornerLift (modularCornerInclusion (H := H) n) 0 = 0
    exact map_zero (isometricCornerLiftHom (modularCornerInclusion (H := H) n))
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change isometricCornerLift (modularCornerInclusion (H := H) n) 1 = modularFiniteProjection (H := H) n
    exact modularCornerInclusion_projection (H := H) n
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change isometricCornerLift (modularCornerInclusion (H := H) n) (a.val + b.val) =
      isometricCornerLift (modularCornerInclusion (H := H) n) a.val +
        isometricCornerLift (modularCornerInclusion (H := H) n) b.val
    exact map_add (isometricCornerLiftHom (modularCornerInclusion (H := H) n)) a.val b.val
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change isometricCornerLift (modularCornerInclusion (H := H) n) (a.val * b.val) =
      isometricCornerLift (modularCornerInclusion (H := H) n) a.val *
        isometricCornerLift (modularCornerInclusion (H := H) n) b.val
    exact isometricCornerLift_mul _ a.val b.val
  commutes' c := by
    apply Subtype.ext
    apply Subtype.ext
    change isometricCornerLift (modularCornerInclusion (H := H) n) (c • 1) = c • modularFiniteProjection (H := H) n
    change isometricCornerLiftHom (modularCornerInclusion (H := H) n) (c • 1) = _
    rw [map_smul]
    exact congrArg (fun T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) => c • T)
      (modularCornerInclusion_projection (H := H) n)
  map_star' a := by
    apply Subtype.ext
    apply Subtype.ext
    change isometricCornerLift (modularCornerInclusion (H := H) n) (star a.val) =
      star (isometricCornerLift (modularCornerInclusion (H := H) n) a.val)
    exact isometricCornerLift_star _ a.val

lemma modularCornerToAbstract_injective (S : StandardModularData H) (n : ℕ) :
    Function.Injective (modularCornerToAbstract S n) := by
  intro a b h
  apply Subtype.ext
  apply isometricCornerLift_injective (modularCornerInclusion (H := H) n)
  exact congrArg (fun z : ModularFiniteCorner S n => z.val.val) h


def modularCompressedTracialStateFormula (S : StandardModularData H) (n : ℕ) :
    Pureness.TracialState (modularCompressedCorner S (n + 1)).toStarSubalgebra :=
  tracialStatePullback (modularFiniteCornerTracialState S n)
    (modularCornerToAbstract S (n + 1))

private theorem exists_modularCompressedTracialState (S : StandardModularData H) (n : ℕ) :
    ∃ τ : Pureness.TracialState (modularCompressedCorner S (n + 1)).toStarSubalgebra,
      τ = modularCompressedTracialStateFormula S n := ⟨_, rfl⟩

/-- The constructed state is selected through its proved specification, so
GNS instance reduction does not unfold the entire modular weight construction. -/
def modularCompressedTracialState (S : StandardModularData H) (n : ℕ) :
    Pureness.TracialState (modularCompressedCorner S (n + 1)).toStarSubalgebra :=
  Classical.choose (exists_modularCompressedTracialState S n)

lemma modularCompressedTracialState_eq (S : StandardModularData H) (n : ℕ) :
    modularCompressedTracialState S n = modularCompressedTracialStateFormula S n :=
  Classical.choose_spec (exists_modularCompressedTracialState S n)

lemma modularCompressedTracialState_faithful (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S (n + 1)).toStarSubalgebra)
    (ha : (modularCompressedTracialState S n).functional (star a * a) = 0) : a = 0 := by
  have hval := congrArg
    (fun τ : Pureness.TracialState (modularCompressedCorner S (n + 1)).toStarSubalgebra =>
      τ.functional (star a * a)) (modularCompressedTracialState_eq S n)
  have haf := hval.symm.trans ha
  exact tracialStatePullback_faithful (modularFiniteCornerTracialState S n)
    (modularCornerToAbstract S (n + 1)) (modularCornerToAbstract_injective S (n + 1))
    (modularFiniteCornerTracialState_faithful S n) a haf

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

theorem nuclear_quotient_modular_corner_expectation
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) (n : ℕ) :
    ∃ E : (ModularCornerHilbert (H := H) n →L[ℂ] ModularCornerHilbert (H := H) n) →L[ℂ]
        (ModularCornerHilbert (H := H) n →L[ℂ] ModularCornerHilbert (H := H) n),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ modularCompressedCorner S n) ∧
      (∀ T, T ∈ modularCompressedCorner S n → E T = T) := by
  obtain ⟨Q, hQ, hQn, hQr, hQf⟩ :=
    nuclear_quotient_modular_core_expectation ω hω hA q hq π S hS
  exact ⟨isometricCornerExpectation (modularCornerInclusion (H := H) n) Q,
    isometricCornerExpectation_cp _ Q hQ, isometricCornerExpectation_norm_le _ Q hQn,
    isometricCornerExpectation_mem _ _ _ Q hQr,
    isometricCornerExpectation_fixed _ _ _ Q hQf⟩

end WeakPureInfiniteness

end

end OAI
