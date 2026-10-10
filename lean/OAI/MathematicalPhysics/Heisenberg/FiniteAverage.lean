import OAI.MathematicalPhysics.Heisenberg.SpinBulk

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Average
variable {X E : Type*} [DecidableEq X] [NormedAddCommGroup E]

lemma norm_sum_sub_le (Λ Ξ : Finset X) (f : X → E) (C : ℝ)
    (hf : ∀ x,‖f x‖≤C) :
    ‖∑ x∈Λ,f x-∑ x∈Ξ,f x‖≤((Λ\Ξ).card+(Ξ\Λ).card:ℝ)*C := by
  rw [←Finset.sum_sdiff_sub_sum_sdiff]
  calc _ ≤ ‖∑ x∈Λ\Ξ,f x‖+‖∑ x∈Ξ\Λ,f x‖ := norm_sub_le _ _
       _ ≤ (∑ _∈Λ\Ξ,C)+(∑ _∈Ξ\Λ,C) := add_le_add
         ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _=>hf x)))
         ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _=>hf x)))
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,add_mul]

lemma norm_sum_bulk_le (Λ F : Finset X) (hF : F⊆Λ) (f : X → E) (δ C : ℝ)
    (hgood : ∀ x∈F,‖f x‖≤δ) (hall : ∀ x∈Λ,‖f x‖≤C) :
    ‖∑ x∈Λ,f x‖≤(F.card:ℝ)*δ+((Λ\F).card:ℝ)*C := by
  rw [←Finset.sum_sdiff hF]
  calc _ ≤ ‖∑ x∈Λ\F,f x‖+‖∑ x∈F,f x‖ := norm_add_le _ _
       _ ≤ (∑ _∈Λ\F,C)+(∑ _∈F,δ) := add_le_add
         ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun x hx=>hall x (Finset.mem_sdiff.mp hx).1)))
         ((norm_sum_le _ _).trans (Finset.sum_le_sum hgood))
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

lemma norm_uniform_bulk_le (Λ F : Finset X) (hΛ : Λ.Nonempty) (hF : F⊆Λ)
    (f : X → ℂ) {δ C : ℝ} (hδ : 0≤δ)
    (hgood : ∀ x∈F,‖f x‖≤δ) (hall : ∀ x∈Λ,‖f x‖≤C) :
    ‖(Λ.card:ℂ)⁻¹*∑ x∈Λ,f x‖≤δ+(((Λ\F).card:ℝ)/(Λ.card:ℝ))*C := by
  have hp : (0:ℝ)<Λ.card := by exact_mod_cast Finset.card_pos.mpr hΛ
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  calc _ ≤ (Λ.card:ℝ)⁻¹*((F.card:ℝ)*δ+((Λ\F).card:ℝ)*C) :=
         mul_le_mul_of_nonneg_left (norm_sum_bulk_le Λ F hF f δ C hgood hall) (inv_nonneg.mpr hp.le)
       _ ≤ (Λ.card:ℝ)⁻¹*((Λ.card:ℝ)*δ+((Λ\F).card:ℝ)*C) := by
         gcongr
       _ = _ := by field_simp

end Heisenberg.Average
end
end

end OAI
