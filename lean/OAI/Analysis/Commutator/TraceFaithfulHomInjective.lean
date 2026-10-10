import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
lemma traceFaithfulHom_injective (φ : A →⋆ₐ[ℂ] B) (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
    (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (htrace : ∀ a,ρ (φ a)=τ a) :
    Function.Injective φ := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hfaith
  rw [←htrace,map_mul,map_star,map_sub,hab,sub_self,star_zero,mul_zero,map_zero]

end Kadison

end

end
end

end OAI
