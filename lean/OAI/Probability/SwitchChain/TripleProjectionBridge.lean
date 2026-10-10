import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleProjectionBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_sum_bound {ι : Type*} [Fintype ι]
    (x : E) (y : ι → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    (∑ i, ‖y i‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  have hi : ⟪x, ∑ i, y i⟫ = ∑ i, ‖y i‖ ^ 2 := by
    simp [inner_sum, horth]
  have hnorm := sq_nonneg ‖(2 : ℝ) • x - ∑ i, y i‖
  rw [norm_sub_sq_real] at hnorm
  norm_num [norm_smul, inner_smul_left, hi] at hnorm
  nlinarith

theorem triple_gap_of_row_variance (x : E) (y : Fin 3 → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    ‖x‖ ^ 2 ≤ ⟪x, ∑ i, (x - y i)⟫ := by
  have hb := projection_sum_bound x y horth hvar
  have hi : ⟪x, ∑ i, (x - y i)⟫ =
      3 * ‖x‖ ^ 2 - ∑ i, ‖y i‖ ^ 2 := by
    rw [inner_sum]
    simp only [inner_sub_right, horth, real_inner_self_eq_norm_sq]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hi]
  linarith

theorem square_bound_of_unit_gap (x z : E) (hgap : ‖x‖ ^ 2 ≤ ⟪x, z⟫) :
    ⟪x, z⟫ ≤ ‖z‖ ^ 2 := by
  have hnorm := sq_nonneg ‖x - z‖
  rw [norm_sub_sq_real] at hnorm
  linarith

theorem triple_square_of_row_variance (x : E) (y : Fin 3 → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    ⟪x, ∑ i, (x - y i)⟫ ≤ ‖∑ i, (x - y i)‖ ^ 2 :=
  square_bound_of_unit_gap x _ (triple_gap_of_row_variance x y horth hvar)

theorem triple_square_of_centered_row_variance
    (P : Fin 3 → E →ₗ[ℝ] E) (C : E → E)
    (hsymm : ∀ i, (P i).IsSymmetric)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hfix : ∀ i x, P i (C x) = C x)
    (hvar : ∀ x, ‖∑ i, P i (x - C x)‖ ^ 2 ≤
      2 * ∑ i, ‖P i (x - C x)‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  intro x
  have horth : ∀ i, ⟪x - C x, P i (x - C x)⟫ =
      ‖P i (x - C x)‖ ^ 2 := by
    intro i
    have hi := hsymm i (x - C x) (P i (x - C x))
    rw [hidem] at hi
    rw [← hi, real_inner_self_eq_norm_sq]
  have heq : (∑ i, ((x - C x) - P i (x - C x))) =
      ∑ i, (x - P i x) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sub, hfix]
    abel
  have hzero : ⟪C x, ∑ i, (x - P i x)⟫ = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [inner_sub_right, ← hsymm i (C x) x, hfix, sub_self]
  have h := triple_square_of_row_variance (x - C x)
    (fun i => P i (x - C x)) horth (hvar x)
  rw [heq, inner_sub_left, hzero, sub_zero] at h
  exact h

end Problem315.TripleProjectionBridge

end

end OAI
