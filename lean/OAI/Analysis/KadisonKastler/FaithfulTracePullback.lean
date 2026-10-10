import OAI.Analysis.KadisonKastler.PublishedFock

namespace OAI

/-! # Pulling a faithful trace back through an injective star map -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def FaithfulTracialState.comap (τ : FaithfulTracialState B) (f : A →⋆ₐ[ℂ] B)
    (hf : Function.Injective f) : FaithfulTracialState A where
  toLinearMap := τ.toLinearMap.comp f.toLinearMap
  map_one := by
    change τ.toLinearMap (f 1) = 1
    exact (congrArg τ.toLinearMap (_root_.map_one f)).trans τ.map_one
  positive x := by
    change 0 ≤ (τ.toLinearMap (f (star x * x))).re
    simpa only [map_mul, map_star] using τ.positive (f x)
  positive_im x := by
    change (τ.toLinearMap (f (star x * x))).im = 0
    simpa only [map_mul, map_star] using τ.positive_im (f x)
  faithful x hx := by
    apply hf
    rw [map_zero]
    apply τ.faithful
    change τ.toLinearMap (f (star x * x)) = 0 at hx
    simpa only [map_mul, map_star] using hx
  tracial x y := by
    change τ.toLinearMap (f (x * y)) = τ.toLinearMap (f (y * x))
    simpa only [map_mul] using τ.tracial (f x) (f y)

@[simp] theorem FaithfulTracialState.comap_apply (τ : FaithfulTracialState B)
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) (x : A) :
    (τ.comap f hf).toLinearMap x = τ.toLinearMap (f x) := rfl

theorem starAlgHom_codRestrict_surjective (f : A →⋆ₐ[ℂ] B)
    (S : StarSubalgebra ℂ B) (hf : ∀ a, f a ∈ S)
    (hs : ∀ b : B, b ∈ S → ∃ a, f a = b) :
    Function.Surjective (f.codRestrict S hf) := by
  intro b
  obtain ⟨a, ha⟩ := hs b.val b.property
  exact ⟨a, Subtype.ext ha⟩

end

end KadisonKastler

end OAI
