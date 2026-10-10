import OAI.NumberTheory.JointDickman.Analysis.MellinShortComparison
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! # The two transition strips of a smooth logarithmic window -/
namespace JointDickman
open Finset

theorem logarithmic_boundary_widths {x η δ : ℝ} (hx : 0 ≤ x)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    x * (Real.exp (η * δ) - 1) ≤ 2 * η * δ * x ∧
      x * Real.exp δ - x * Real.exp ((1 - η) * δ) ≤ 6 * η * δ * x := by
  have ht : 0 ≤ η * δ := mul_nonneg hη hδ
  have ht1 : η * δ ≤ 1 := (mul_le_mul hη1 hδ1 hδ (by norm_num)).trans_eq (one_mul 1)
  have hp := Real.abs_exp_sub_one_le (show |η * δ| ≤ 1 by rwa [abs_of_nonneg ht])
  have hm := Real.abs_exp_sub_one_le (show |-(η * δ)| ≤ 1 by simpa only [abs_neg, abs_of_nonneg ht] using ht1)
  have hlo : Real.exp (η * δ) - 1 ≤ 2 * η * δ := by
    rw [abs_of_nonneg ht] at hp
    exact (le_abs_self _).trans (by simpa only [mul_assoc] using hp)
  have hhi : 1 - Real.exp (-(η * δ)) ≤ 2 * η * δ := by
    rw [abs_neg, abs_of_nonneg ht] at hm
    have hh := (neg_le_abs (Real.exp (-(η * δ)) - 1)).trans hm
    linarith
  have hexp : Real.exp δ ≤ 3 :=
    (Real.exp_le_exp.mpr hδ1).trans Real.exp_one_lt_three.le
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hlo hx]
  · have he : Real.exp ((1 - η) * δ) = Real.exp δ * Real.exp (-(η * δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hmul := mul_le_mul_of_nonneg_left hhi (mul_nonneg hx (Real.exp_pos δ).le)
    have hcap := mul_le_mul_of_nonneg_right hexp (mul_nonneg hx ht)
    nlinarith

lemma nat_interval_card_le_length {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Ioc ⌊a⌋₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 1 := by
  have he : a + (b - a) = b := by ring
  simpa only [he] using mellin_short_interval_card_le ha (sub_nonneg.mpr hab)

theorem logarithmic_boundary_card {x η δ : ℝ} (hx : 0 ≤ x)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ((Ioc ⌊x⌋₊ ⌊x * Real.exp (η * δ)⌋₊).card : ℝ) +
      ((Ioc ⌊x * Real.exp ((1 - η) * δ)⌋₊ ⌊x * Real.exp δ⌋₊).card : ℝ) ≤
        8 * η * δ * x + 2 := by
  have hlo : x ≤ x * Real.exp (η * δ) := by
    have hh : 1 ≤ Real.exp (η * δ) := Real.one_le_exp_iff.mpr (mul_nonneg hη hδ)
    nlinarith
  have hhi : x * Real.exp ((1 - η) * δ) ≤ x * Real.exp δ := by
    apply mul_le_mul_of_nonneg_left _ hx
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcount1 := nat_interval_card_le_length hx hlo
  have hcount2 := nat_interval_card_le_length
    (mul_nonneg hx (Real.exp_pos _).le) hhi
  obtain ⟨hw1, hw2⟩ := logarithmic_boundary_widths hx hη hη1 hδ hδ1
  nlinarith

end JointDickman

end OAI
