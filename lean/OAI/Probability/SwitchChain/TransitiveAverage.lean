import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TransitiveAverage

variable {Γ X : Type*} [Group Γ] [Fintype Γ] [sectionFintypeX : Fintype X]
  [MulAction Γ X] [MulAction.IsPretransitive Γ X]

include sectionFintypeX in
theorem sum_smul_eq (f : X → ℝ) (x y : X) :
    (∑ g : Γ, f (g • x)) = ∑ g : Γ, f (g • y) := by
  have retainedsectionFintypeX := sectionFintypeX
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq Γ x y
  symm
  simp_rw [smul_smul]
  exact Equiv.sum_comp (Equiv.mulRight a) (fun g : Γ => f (g • x))

theorem card_mul_sum_smul (f : X → ℝ) (x : X) :
    (Fintype.card X : ℝ) * (∑ g : Γ, f (g • x)) =
      (Fintype.card Γ : ℝ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℝ) * (∑ g : Γ, f (g • x)) =
        ∑ _y : X, ∑ g : Γ, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : Γ, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_smul_eq f x y
    _ = ∑ g : Γ, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : Γ, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Equiv.sum_comp (MulAction.toPerm g) f
    _ = (Fintype.card Γ : ℝ) * (∑ y : X, f y) := by simp

theorem average_smul_eq (f : X → ℝ) (x : X) :
    (∑ g : Γ, f (g • x)) / (Fintype.card Γ : ℝ) =
      (∑ y : X, f y) / (Fintype.card X : ℝ) := by
  have : Nonempty X := ⟨x⟩
  have hΓ : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hΓ hX).mpr
  simpa only [mul_comm] using card_mul_sum_smul (Γ := Γ) f x

theorem average_sum_sq_difference (f : X → ℝ) :
    (∑ g : Γ, ∑ x : X, (f x - f (g • x)) ^ 2) / (Fintype.card Γ : ℝ) =
      (∑ x : X, ∑ y : X, (f x - f y) ^ 2) / (Fintype.card X : ℝ) := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Finset.sum_div] using
    average_smul_eq (Γ := Γ) (fun y => (f x - f y) ^ 2) x

end Problem315.TransitiveAverage

end

end OAI
