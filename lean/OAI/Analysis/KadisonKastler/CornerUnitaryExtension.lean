import OAI.Analysis.KadisonKastler.FiniteBlockExtension

namespace OAI

/-! # Extending corner unitaries by the identity

Finite signed groups in a proper matrix corner act as the identity on
its complementary subspace. These algebraic identities retain that action.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
  [Ring B] [StarRing B] [_root_.Algebra ℂ B]

/-- Adding the complementary identity respects multiplication on the range
of a nonunital star homomorphism. -/
theorem add_complement_mul (φ : A →⋆ₙₐ[ℂ] B) (a b : A) :
    (φ a + (1 - φ 1)) * (φ b + (1 - φ 1)) = φ (a * b) + (1 - φ 1) := by
  have hl (x : A) : φ x * (1 - φ 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]
  have hr (x : A) : (1 - φ 1) * φ x = 0 := by
    rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]
  have hp : (1 - φ 1) * (1 - φ 1) = 1 - φ 1 := by
    rw [sub_mul, one_mul, hl 1, sub_zero]
  rw [add_mul, mul_add, mul_add, hl, hr, hp, add_zero, zero_add, ← map_mul]

/-- A unitary in a represented corner is a unitary on the whole space after
adding the complementary identity. -/
def cornerUnitaryExtension (φ : A →⋆ₙₐ[ℂ] B) : unitary A →* unitary B where
  toFun u := ⟨φ u.val + (1 - φ 1), by
    constructor
    · change star (φ u.val + (1 - φ 1)) * (φ u.val + (1 - φ 1)) = 1
      rw [star_add, star_sub, star_one, ← map_star, ← map_star, star_one,
        add_complement_mul, u.property.1]
      abel
    · change (φ u.val + (1 - φ 1)) * star (φ u.val + (1 - φ 1)) = 1
      rw [star_add, star_sub, star_one, ← map_star, ← map_star, star_one,
        add_complement_mul, u.property.2]
      abel⟩
  map_one' := Subtype.ext (by change φ 1 + (1 - φ 1) = 1; abel)
  map_mul' u v := Subtype.ext (add_complement_mul φ u.val v.val).symm

@[simp]
theorem cornerUnitaryExtension_coe (φ : A →⋆ₙₐ[ℂ] B) (u : unitary A) :
    (cornerUnitaryExtension φ u : B) = φ u.val + (1 - φ 1) := rfl

end

end KadisonKastler

end OAI
