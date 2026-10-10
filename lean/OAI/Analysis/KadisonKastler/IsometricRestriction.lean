import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-! # Restricting a representation through a reducing isometry

Compression by an isometry is multiplicative when its range projection
commutes with the represented algebra. The intertwining identity is kept
explicit for later weak-continuity and faithfulness arguments.
-/

namespace KadisonKastler

noncomputable section

theorem isometry_equiv_comp_projection
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : F ≃ₗᵢ[ℂ] G) (J : E →ₗᵢ[ℂ] F) :
    (U.toLinearIsometry.comp J).toContinuousLinearMap.comp
        (U.toLinearIsometry.comp J).toContinuousLinearMap.adjoint =
      U.conjStarAlgEquiv (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) := by
  change ((U : F →L[ℂ] G).comp J.toContinuousLinearMap).comp
    ((U : F →L[ℂ] G).comp J.toContinuousLinearMap).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, U.adjoint_eq_symm,
    LinearIsometryEquiv.conjStarAlgEquiv_apply]
  simp only [ContinuousLinearMap.comp_assoc]

variable {E F A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [CStarAlgebra A]

theorem isometry_adjoint_apply (J : E →ₗᵢ[ℂ] F) (x : E) :
    J.toContinuousLinearMap.adjoint (J x) = x :=
  DFunLike.congr_fun J.adjoint_comp_self x

def isometricCompression (J : E →ₗᵢ[ℂ] F) (T : F →L[ℂ] F) : E →L[ℂ] E :=
  J.toContinuousLinearMap.adjoint.comp (T.comp J.toContinuousLinearMap)

theorem isometricCompression_intertwines (J : E →ₗᵢ[ℂ] F) (T : F →L[ℂ] F)
    (hT : T * (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) =
      (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) * T) (x : E) :
    J (isometricCompression J T x) = T (J x) := by
  have h := DFunLike.congr_fun hT (J x)
  change T (J (J.toContinuousLinearMap.adjoint (J x))) =
    J (J.toContinuousLinearMap.adjoint (T (J x))) at h
  rw [isometry_adjoint_apply] at h
  exact h.symm

def isometricRestriction (J : E →ₗᵢ[ℂ] F) (π : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hπ : ∀ a, π a * (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) =
      (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) * π a) :
    A →⋆ₐ[ℂ] (E →L[ℂ] E) where
  toFun a := isometricCompression J (π a)
  map_zero' := by ext x; simp [isometricCompression]
  map_one' := by
    ext x
    change J.toContinuousLinearMap.adjoint (π 1 (J x)) = x
    rw [map_one]
    exact isometry_adjoint_apply J x
  map_add' a b := by ext x; simp [isometricCompression]
  map_mul' a b := by
    ext x
    have h := isometricCompression_intertwines J (π b) (hπ b) x
    change J.toContinuousLinearMap.adjoint (π (a * b) (J x)) =
      J.toContinuousLinearMap.adjoint (π a (J (isometricCompression J (π b) x)))
    rw [h, map_mul]
    rfl
  commutes' c := by
    ext x
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    change J.toContinuousLinearMap.adjoint (c • J x) = c • x
    rw [map_smul, isometry_adjoint_apply]
  map_star' a := by
    change J.toContinuousLinearMap.adjoint.comp ((π (star a)).comp J.toContinuousLinearMap) =
      star (J.toContinuousLinearMap.adjoint.comp ((π a).comp J.toContinuousLinearMap))
    simp only [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

@[simp] theorem isometricRestriction_apply (J : E →ₗᵢ[ℂ] F)
    (π : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hπ : ∀ a, π a * (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) =
      (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint) * π a)
    (a : A) (x : E) :
    J (isometricRestriction J π hπ a x) = π a (J x) :=
  isometricCompression_intertwines J (π a) (hπ a) x

end

end KadisonKastler

end OAI
