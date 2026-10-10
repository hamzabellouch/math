import OAI.Analysis.Nuclearity.CPMultiplicativeDefect

namespace OAI

/-! A unital completely positive extension of a representation is bimodular
on that representation. This is the Schwarz-equality step used when extending
a commuting tensor representation to obtain a commutant-valued projection. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] in
lemma cp_extension_representation_mul_left (ι : A →⋆ₐ[ℂ] B) (π : A →⋆ₐ[ℂ] C)
    (Φ : B →L[ℂ] C) (hΦ : CompletelyPositive Φ) (he : ∀ a, Φ (ι a) = π a)
    (a : A) (b : B) : Φ (ι a * b) = π a * Φ b := by
  have h1 : Φ 1 = 1 := by simpa only [map_one] using he 1
  have hz : Φ (ι a * star (ι a)) - Φ (ι a) * star (Φ (ι a)) = 0 := by
    rw [← map_star, ← map_mul, he, he, map_mul, map_star, sub_self]
  have hh := completelyPositive_mul_error_le hΦ h1 (ι a) b
  rw [hz, norm_zero, Real.sqrt_zero, zero_mul] at hh
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))).trans
    (by rw [he])

omit [PartialOrder A] [StarOrderedRing A] in
lemma cp_extension_representation_mul_right (ι : A →⋆ₐ[ℂ] B) (π : A →⋆ₐ[ℂ] C)
    (Φ : B →L[ℂ] C) (hΦ : CompletelyPositive Φ) (he : ∀ a, Φ (ι a) = π a)
    (a : A) (b : B) : Φ (b * ι a) = Φ b * π a := by
  have hh := congrArg star (cp_extension_representation_mul_left ι π Φ hΦ he (star a) (star b))
  simpa only [map_star, ← completelyPositive_map_star hΦ, star_mul, star_star] using hh

omit [PartialOrder A] [StarOrderedRing A] in
lemma cp_extension_commutes (ι : A →⋆ₐ[ℂ] B) (π : A →⋆ₐ[ℂ] C)
    (Φ : B →L[ℂ] C) (hΦ : CompletelyPositive Φ) (he : ∀ a, Φ (ι a) = π a)
    (b : B) (hb : ∀ a, Commute (ι a) b) (a : A) : Commute (π a) (Φ b) := by
  change π a * Φ b = Φ b * π a
  rw [← cp_extension_representation_mul_left ι π Φ hΦ he,
    (hb a).eq, cp_extension_representation_mul_right ι π Φ hΦ he]

end WeakPureInfiniteness

end

end OAI
