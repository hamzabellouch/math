import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.AffineUniformCoordinates

namespace OAI

namespace Balanced.AffineTargetError

theorem sum_error_of_eq_off {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (heq : ∀ x, x ∉ S → f x = g x) :
    |(∑ x, f x) - ∑ x, g x| ≤ (S.card : ℝ) := by
  calc
    |(∑ x, f x) - ∑ x, g x| = |∑ x, (f x - g x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, |f x - g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, if x ∈ S then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ S
      · rw [ite_eq_left hx, abs_le]
        constructor <;> linarith [(hf x).1, (hf x).2, (hg x).1, (hg x).2]
      · simp [hx, heq x hx]
    _ = (S.card : ℝ) := by simp

theorem average_error_of_eq_off {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (heq : ∀ x, x ∉ S → f x = g x) :
    |((∑ x, f x) / (Fintype.card α : ℝ)) -
      (∑ x, g x) / (Fintype.card α : ℝ)| ≤ (S.card : ℝ) / Fintype.card α := by
  rw [← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card α from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (sum_error_of_eq_off S f g hf hg heq) (Nat.cast_nonneg _)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem target_card (l : Line F) : (linePoints l).card = Fintype.card F := by
  rcases l with ⟨d, a⟩
  cases d with
  | none => exact PairEvaluation.linePoints_card_via_coordinates none (some 0) (by simp) a
  | some m => exact PairEvaluation.linePoints_card_via_coordinates (some m) none (by simp) a

theorem plane_average_error (l : Line F) (f g : Point F → ℝ)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (heq : ∀ p, ¬ OnLine p l → f p = g p) :
    |((∑ p, f p) / (Fintype.card F : ℝ) ^ 2) -
      (∑ p, g p) / (Fintype.card F : ℝ) ^ 2| ≤ 1 / Fintype.card F := by
  have h := average_error_of_eq_off (linePoints l) f g hf hg (by
    intro p hp
    apply heq p
    simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] using hp)
  have hcard : Fintype.card (Point F) = Fintype.card F * Fintype.card F := Fintype.card_prod _ _
  rw [target_card, hcard, Nat.cast_mul] at h
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hratio : (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) * Fintype.card F) =
      1 / Fintype.card F := by field_simp
  simpa only [pow_two, hratio] using h

end Balanced.AffineTargetError

end OAI
