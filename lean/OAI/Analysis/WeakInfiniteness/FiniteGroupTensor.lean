import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteDiagonalState
import OAI.Analysis.WeakInfiniteness.FullGroupAlgebra
import OAI.Analysis.WeakInfiniteness.LiftedHilbert
import OAI.Analysis.WeakInfiniteness.SpatialVectorStates

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

section TensorConjugation

variable {H K L M : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

lemma tensor_map_conj (e : H ≃ₗᵢ[ℂ] L) (f : K ≃ₗᵢ[ℂ] M)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K) (ξ : H ⊗[ℂ] K) :
    TensorProduct.mapL (e.conjStarAlgEquiv S) (f.conjStarAlgEquiv T)
      (TensorProduct.congrIsometry e f ξ) =
      TensorProduct.congrIsometry e f (TensorProduct.mapL S T ξ) := by
  induction ξ using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorConjugation

section FiniteGroupSpatial

variable {G F : Type u} [Group G] [Group F] [Fintype F] [DecidableEq F]

abbrev finiteGroupRepresentation (q : G →* F) : GroupRepresentation G where
  hilbert := ⟨EuclideanSpace ℂ F⟩
  group := (finiteLeftRegular F).comp q

abbrev finiteGroupSpatialRepresentation (q : G →* F) :
    SpatialRepresentation (FullGroupAlgebra G) (FullGroupAlgebra G) where
  left := ⟨ULift.{u+1} (EuclideanSpace ℂ F)⟩
  right := ⟨ULift.{u+1} (EuclideanSpace ℂ F)⟩
  leftRep := ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (fullGroupEvaluation (finiteGroupRepresentation q))).toNonUnitalStarAlgHom
  rightRep := ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (fullGroupEvaluation (finiteGroupRepresentation q))).toNonUnitalStarAlgHom

def finiteGroupSpatialDiagonal (_q : G →* F) :
    ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F) :=
  TensorProduct.congrIsometry (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F)

lemma norm_finiteGroupSpatialDiagonal (q : G →* F) : ‖finiteGroupSpatialDiagonal q‖ = 1 := by
  unfold finiteGroupSpatialDiagonal
  exact (LinearIsometryEquiv.norm_map _ _).trans (norm_normalizedFiniteDiagonalVector F)

lemma finiteGroupSpatialDiagonal_coefficient (q : G →* F) (s t : G) :
    spatialVectorFunctional (finiteGroupSpatialRepresentation q)
      (finiteGroupSpatialDiagonal q : Completion
        (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
      (spatialElementary (fullGroupElement s) (fullGroupElement t)) =
      if q s = q t then (1 : ℂ) else 0 := by
  rw [spatialVectorFunctional_elementary]
  change inner ℂ (TensorProduct.congrIsometry
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F)) (TensorProduct.mapL
    ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv (finiteLeftRegular F (q s)))
    ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv (finiteLeftRegular F (q t)))
    (TensorProduct.congrIsometry
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F))) = _
  rw [tensor_map_conj]
  exact (LinearIsometryEquiv.inner_map_map ..).trans
    (normalizedFiniteDiagonalVector_inner_translate F (q s) (q t))

end FiniteGroupSpatial

end WeakPureInfiniteness
end

end OAI
