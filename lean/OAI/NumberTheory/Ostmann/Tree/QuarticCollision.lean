import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
variable {F : Type*} [Field F]

theorem pair_sum_product_identifies {b₁ b₂ b₃ b₄ : F}
    (hs : b₁+b₂=b₃+b₄) (hp : b₁*b₂=b₃*b₄) :
    (b₁=b₃ ∧ b₂=b₄) ∨ (b₁=b₄ ∧ b₂=b₃) := by
  have hz : (b₁-b₃)*(b₁-b₄)=0 := by
    linear_combination b₁*hs-hp
  rcases mul_eq_zero.mp hz with h | h
  · left
    have h13 := sub_eq_zero.mp h
    exact ⟨h13, by linear_combination hs-h13⟩
  · right
    have h14 := sub_eq_zero.mp h
    exact ⟨h14, by linear_combination hs-h14⟩

theorem quartet_collision_two_roots {b₁ b₂ b₃ b₄ a a' : F}
    (ha : (a-b₁)*(a-b₂)=(a-b₃)*(a-b₄))
    (ha' : (a'-b₁)*(a'-b₂)=(a'-b₃)*(a'-b₄)) (hne : a ≠ a') :
    (b₁=b₃ ∧ b₂=b₄) ∨ (b₁=b₄ ∧ b₂=b₃) := by
  have hm : (a-a')*((b₁+b₂)-(b₃+b₄))=0 := by linear_combination ha'-ha
  have hs : b₁+b₂=b₃+b₄ := sub_eq_zero.mp
    ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne))
  have hp : b₁*b₂=b₃*b₄ := by linear_combination ha+a*hs
  exact pair_sum_product_identifies hs hp

theorem quartet_collision_card_le_one [Fintype F] [DecidableEq F]
    (b₁ b₂ b₃ b₄ : F)
    (hdiag : ¬((b₁=b₃ ∧ b₂=b₄) ∨ (b₁=b₄ ∧ b₂=b₃))) :
    (Finset.univ.filter (fun a : F => (a-b₁)*(a-b₂)=(a-b₃)*(a-b₄))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha a' ha'
  by_contra hne
  exact hdiag (quartet_collision_two_roots (Finset.mem_filter.mp ha).2
    (Finset.mem_filter.mp ha').2 hne)

end
end Ostmann.FiniteField

end OAI
