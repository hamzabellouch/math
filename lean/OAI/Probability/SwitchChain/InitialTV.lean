import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315Aux

def deltaUniformTV {α : Type*} [Fintype α] (x : α) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ y : α,
    |(if x = y then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)|

theorem deltaUniformTV_eq_zero_of_card_one {α : Type*} [Fintype α]
    (h : Fintype.card α = 1) (x : α) : deltaUniformTV x = 0 := by
  classical
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have heq : ∀ y : α, x = y := fun y => Subsingleton.elim x y
  unfold deltaUniformTV
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  simp [heq y, h]

theorem deltaUniformTV_eq {α : Type*} [Fintype α] (x : α) :
    deltaUniformTV x = 1 - 1 / (Fintype.card α : ℝ) := by
  classical
  have : Nonempty α := ⟨x⟩
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc1 : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hi : (1 : ℝ) / Fintype.card α ≤ 1 := (div_le_one hc).2 hc1
  have hi0 : (0 : ℝ) ≤ 1 / Fintype.card α := le_of_lt (one_div_pos.mpr hc)
  have habs (y : α) :
      |(if x = y then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)| =
      (if x = y then 1 - 2 / (Fintype.card α : ℝ) else 0) +
        1 / (Fintype.card α : ℝ) := by
    by_cases hxy : x = y
    · simp only [hxy, ite_true, abs_of_nonneg (sub_nonneg.mpr hi)]
      ring
    · simp only [hxy, ite_false, zero_sub, abs_neg, abs_of_nonneg hi0, zero_add]
  unfold deltaUniformTV
  simp_rw [habs]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [ne_of_gt hc]
  ring

theorem sum_sq_delta_uniform_eq {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    (∑ y : α, ((if x = y then (1 : ℝ) else 0) -
      1 / (Fintype.card α : ℝ)) ^ 2) = 1 - 1 / (Fintype.card α : ℝ) := by
  classical
  have : Nonempty α := ⟨x⟩
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hterm (y : α) :
      ((if x = y then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)) ^ 2 =
      (if x = y then 1 - 2 / (Fintype.card α : ℝ) else 0) +
        (1 / (Fintype.card α : ℝ)) ^ 2 := by
    by_cases hxy : x = y <;> simp only [hxy, ite_true, ite_false] <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [ne_of_gt hc]
  ring

end Problem315Aux

end

end OAI
