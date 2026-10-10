import OAI.Analysis.KadisonKastler.CompletelyBounded
import OAI.Analysis.KadisonKastler.RectangularCorner
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A star homomorphism, viewed as a continuous linear map. -/
def starAlgHomToContinuousLinearMap (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)

@[simp]
theorem starAlgHomToContinuousLinearMap_apply (φ : A →⋆ₐ[ℂ] B) (a : A) :
    starAlgHomToContinuousLinearMap φ a = φ a := rfl

/-- The scalar isometry underlying a faithful representation. -/
theorem injective_starAlgHom_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (a : A) : ‖φ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map φ hφ a

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Applying a faithful star homomorphism entrywise remains injective. -/
theorem injective_starAlgHom_matrix (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] :
    Function.Injective (CStarMatrix.mapₙₐ (n := n) φ.toNonUnitalStarAlgHom) := by
  intro X Y hXY
  ext i j
  exact hφ (congrArg (fun Z : CStarMatrix n n B => Z i j) hXY)

/-- Faithfulness preserves the norm of each square amplification. -/
theorem injective_starAlgHom_matrix_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  change ‖CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom X‖ = ‖X‖
  exact NonUnitalStarAlgHom.norm_map _ (injective_starAlgHom_matrix φ hφ) X

/-- Every faithful star representation preserves all rectangular matrix norms. -/
theorem injective_starAlgHom_completelyIsometric (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) : CompletelyIsometric φ.toAlgHom.toLinearMap := by
  intro p q X
  calc
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ =
        ‖rectangularCorner (CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap (rectangularCorner X)‖ := by
      rw [rectangularCorner_map]
    _ = ‖rectangularCorner X‖ := injective_starAlgHom_matrix_norm φ hφ _
    _ = ‖X‖ := norm_rectangularCorner X

end

end KadisonKastler

end OAI
