import OAI.Analysis.KadisonKastler.Transport
import Mathlib.Algebra.Star.StarAlgHom

namespace OAI

/-!
# The involution in multiplication correction

This is the algebraic star-preserving part of the UCP criterion. The
linear correction itself remains an explicit hypothesis.
-/

namespace KadisonKastler

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
  [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]

theorem linearEquiv_symm_map_star (F : A ≃ₗ[ℂ] B)
    (hstar : ∀ x, F (star x) = star (F x)) (y : B) :
    F.symm (star y) = star (F.symm y) := by
  apply F.injective
  rw [F.apply_symm_apply, hstar, F.apply_symm_apply]

theorem transportedMul_star (F : A ≃ₗ[ℂ] B)
    (hstar : ∀ x, F (star x) = star (F x)) (x y : A) :
    star (transportedMul F x y) = transportedMul F (star y) (star x) := by
  apply F.injective
  rw [hstar, map_transportedMul, star_mul, map_transportedMul, hstar, hstar]

/-- The star-algebra equivalence furnished by a star-preserving linear
correction of the transported multiplication. -/
noncomputable def correctedStarAlgEquiv (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y)
    (hFstar : ∀ x, F (star x) = star (F x))
    (hLstar : ∀ x, L (star x) = star (L x)) : A ≃⋆ₐ[ℂ] B :=
  { correctedAlgEquiv F L hL with
    map_smul' c x := by
      change F (L.symm (c • x)) = c • F (L.symm x)
      rw [map_smul, map_smul]
    map_star' x := by
      change F (L.symm (star x)) = star (F (L.symm x))
      rw [linearEquiv_symm_map_star L hLstar, hFstar] }

@[simp] theorem correctedStarAlgEquiv_apply (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y)
    (hFstar : ∀ x, F (star x) = star (F x))
    (hLstar : ∀ x, L (star x) = star (L x)) (x : A) :
    correctedStarAlgEquiv F L hL hFstar hLstar x = F (L.symm x) := rfl

end KadisonKastler

end OAI
