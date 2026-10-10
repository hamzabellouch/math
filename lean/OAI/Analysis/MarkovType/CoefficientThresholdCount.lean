import OAI.Analysis.MarkovType.CoefficientBlockIteration
import OAI.Analysis.MarkovType.CoefficientSelectedBlocks
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Positivity

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientBasic_card_large_lt_pow {M : ℕ} {K : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K)
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, y j‖)
    {n : ℕ} (x : Fin n → E) (hx : CoefficientBasic K x) (k : ℕ) :
    (Finset.univ.filter (fun i =>
      (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ < ‖x i‖)).card < M ^ k := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i =>
    (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ < ‖x i‖)
  by_contra h
  have hcard : M ^ k ≤ s.card := Nat.le_of_not_gt h
  let e : Fin (M ^ k) ↪o Fin n := s.orderEmbOfCardLe hcard
  have he (i : Fin (M ^ k)) :
      (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ < ‖x (e i)‖ :=
    (Finset.mem_filter.mp (s.orderEmbOfCardLe_mem hcard i)).2
  let y : Fin (M ^ k) → E := selectedConsecutiveBlocks e x
  have hy : CoefficientBasic K y := hx.selectedConsecutiveBlocks e
  obtain ⟨i, hi⟩ := coefficientBasic_half_gain_iterate hgain k y hy
  have hsum : (∑ j, y j) = ∑ j, x j :=
    sum_selectedConsecutiveBlocks (pow_pos hM k) e x
  rw [hsum] at hi
  have hentry := norm_selected_le_two_mul_block hx e i
  have hbound : ‖x (e i)‖ ≤ (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by
    calc
      ‖x (e i)‖ ≤ (2 * K) * ‖y i‖ := hentry
      _ ≤ (2 * K) * ((1 / 2 : ℝ) ^ k * ‖∑ j, x j‖) :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num) hK)
      _ = _ := by ring
  exact (not_lt_of_ge hbound) (he i)

end MarkovSuperreflexivity

end OAI
