import Mathlib
import OAI.Analysis.Commutator.CenteredSpace
import OAI.Analysis.Commutator.TracialCommutation

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

end TracialGNS

end Kadison

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

end Kadison.TracialGNS

noncomputable section

open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Kadison

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

noncomputable def centeredStar : centeredSpace (vacuum τ) →L⋆[ℂ] centeredSpace (vacuum τ) :=
  ((starMap τ hτ).comp (centeredSpace (vacuum τ)).subtypeL).codRestrict
    (centeredSpace (vacuum τ)) (fun x => by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      change inner ℂ (vacuum τ) (starMap τ hτ (x : τ.GNS)) = 0
      have h := starMap_inner τ hτ (vacuum τ) (x : τ.GNS)
      rw [starMap_vacuum] at h
      rw [h, inner_eq_zero_symm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)

@[simp] lemma centeredStar_coe (x : centeredSpace (vacuum τ)) :
    (centeredStar τ hτ x : τ.GNS) = starMap τ hτ (x : τ.GNS) := rfl

lemma centeredStar_involutive : Function.Involutive (centeredStar τ hτ) := by
  intro x
  apply Subtype.ext
  exact starMap_involutive τ hτ (x : τ.GNS)

end Kadison.TracialGNS
end
end

end OAI
