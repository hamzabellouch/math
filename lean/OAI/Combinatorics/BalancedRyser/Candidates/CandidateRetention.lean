import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace Balanced.CandidateRetention

variable {Tuple Line : Type*} [DecidableEq Line]

theorem card_sq_le_image_card_mul_fiber_sq (tuples : Finset Tuple)
    (line : Tuple → Line) :
    (tuples.card : ℝ) ^ 2 ≤ ((tuples.image line).card : ℝ) *
      ∑ l ∈ tuples.image line, ((tuples.filter (fun t => line t = l)).card : ℝ) ^ 2 := by
  have hsum : (tuples.card : ℝ) =
      ∑ l ∈ tuples.image line, ((tuples.filter (fun t => line t = l)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image line tuples
  rw [hsum]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (tuples.image line)
    (fun _ => (1 : ℝ)) (fun l => ((tuples.filter (fun t => line t = l)).card : ℝ))

theorem fiber_sq_sum_mono [Fintype Line] {valid all : Finset Tuple}
    (hsub : valid ⊆ all) (line : Tuple → Line) :
    (∑ l, ((valid.filter (fun t => line t = l)).card : ℝ) ^ 2) ≤
      ∑ l, ((all.filter (fun t => line t = l)).card : ℝ) ^ 2 := by
  apply Finset.sum_le_sum
  intro l _
  have hc : (valid.filter (fun t => line t = l)).card ≤
      (all.filter (fun t => line t = l)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  have hr : ((valid.filter (fun t => line t = l)).card : ℝ) ≤
      ((all.filter (fun t => line t = l)).card : ℝ) := by exact_mod_cast hc
  exact pow_le_pow_left₀ (by positivity) hr 2

theorem valid_card_sq_le_retained_mul_all_sq [Fintype Line]
    {valid all : Finset Tuple} (hsub : valid ⊆ all) (line : Tuple → Line) :
    (valid.card : ℝ) ^ 2 ≤ ((valid.image line).card : ℝ) *
      ∑ l, ((all.filter (fun t => line t = l)).card : ℝ) ^ 2 := by
  apply (card_sq_le_image_card_mul_fiber_sq valid line).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ l ∈ valid.image line, ((valid.filter (fun t => line t = l)).card : ℝ) ^ 2) ≤
        ∑ l, ((valid.filter (fun t => line t = l)).card : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ ≤ _ := fiber_sq_sum_mono hsub line

theorem retained_card_lower_bound [Fintype Line]
    {valid all : Finset Tuple} (hsub : valid ⊆ all) (line : Tuple → Line)
    {a C q : ℝ} (ha : 0 ≤ a) (hC : 0 < C) (hq : 0 < q)
    (hmass : a * q ≤ valid.card)
    (hsquare : (∑ l, ((all.filter (fun t => line t = l)).card : ℝ) ^ 2) ≤ C * q) :
    (a ^ 2 / C) * q ≤ (valid.image line).card := by
  have hcs := valid_card_sq_le_retained_mul_all_sq hsub line
  have hmasssq : (a * q) ^ 2 ≤ (valid.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha hq.le) hmass 2
  have hupper := mul_le_mul_of_nonneg_left hsquare
    (show (0 : ℝ) ≤ (valid.image line).card by positivity)
  have hmain : a ^ 2 * q ^ 2 ≤ ((valid.image line).card : ℝ) * (C * q) := by
    nlinarith
  have hcancel : a ^ 2 * q ≤ ((valid.image line).card : ℝ) * C := by
    nlinarith
  simpa [div_mul_eq_mul_div] using (div_le_iff₀ hC).mpr hcancel

end Balanced.CandidateRetention

end OAI
