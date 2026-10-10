import OAI.Analysis.KadisonKastler.ModularStateAction
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Faithful vector-state products separate algebra elements -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem eq_of_vectorState_right_products (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M)
    (he : ∀ c ∈ M, productVectorState Ω (a * c) = productVectorState Ω (b * c)) : a = b := by
  let d : Algebra M := ⟨star (a - b), M.toStarSubalgebra.star_mem' (M.sub_mem ha hb)⟩
  have hv : d.val Ω = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ Ω (star (star (a - b)) (d.val Ω)) = 0
    rw [star_star, sub_apply, inner_sub_right]
    exact sub_eq_zero.mpr (he d.val d.property)
  have hd : d = 0 := hsep (show algebraVectorMap M Ω d = algebraVectorMap M Ω 0 by
    rw [map_zero]
    exact hv)
  have hs : star (a - b) = 0 := congrArg Subtype.val hd
  have hh := congrArg star hs
  rw [star_star, star_zero] at hh
  exact sub_eq_zero.mp hh

end

end KadisonKastler

end OAI
