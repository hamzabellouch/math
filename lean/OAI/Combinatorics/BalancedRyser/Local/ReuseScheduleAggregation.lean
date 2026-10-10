import Mathlib.Data.Fintype.Pi
import OAI.Combinatorics.BalancedRyser.Local.ReuseExtensionArithmetic

namespace OAI

namespace Balanced.ReuseSchedule

open scoped BigOperators

def score {n : ℕ} (s : Fin n → Fin 5) : ℕ :=
  ∑ i, reuseSaving (s i).val

theorem product_extension_eq (A q : ℝ) {n : ℕ} (s : Fin n → Fin 5) :
    (∏ i, A / q ^ reuseSaving (s i).val) = A ^ n / q ^ score s := by
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  simp [score]

theorem schedule_bound_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    {n : ℕ} (hn : n ≤ 6) (s : Fin n → Fin 5) (hs : 3 ≤ score s) :
    A ^ n / q ^ score s ≤ (max 1 A) ^ 6 / q ^ 3 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmax : 1 ≤ max 1 A := le_max_left _ _
  have hnum : A ^ n ≤ (max 1 A) ^ 6 :=
    (pow_le_pow_left₀ hA (le_max_right _ _) n).trans
      (pow_le_pow_right₀ hmax hn)
  calc
    A ^ n / q ^ score s ≤ (max 1 A) ^ 6 / q ^ score s :=
      div_le_div_of_nonneg_right hnum (le_of_lt (pow_pos hqpos _))
    _ ≤ (max 1 A) ^ 6 / q ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hqpos _)
        (pow_le_pow_right₀ hq hs)

theorem sum_schedule_bounds_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (n : ℕ) (hn : n ≤ 6) :
    (∑ s : Fin n → Fin 5,
      if 3 ≤ score s then A ^ n / q ^ score s else 0) ≤
        (5 : ℝ) ^ n * ((max 1 A) ^ 6 / q ^ 3) := by
  classical
  calc
    _ ≤ ∑ _s : Fin n → Fin 5, (max 1 A) ^ 6 / q ^ 3 := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs with hs
      · exact schedule_bound_le A q hA hq hn s hs
      · positivity
    _ = _ := by simp

theorem schedule_count : (∑ n : Fin 7, (5 : ℝ) ^ n.val) = 19531 := by
  norm_num [Fin.sum_univ_succ]

theorem sum_all_schedule_bounds_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q) :
    (∑ n : Fin 7, ∑ s : Fin n.val → Fin 5,
      if 3 ≤ score s then A ^ n.val / q ^ score s else 0) ≤
        19531 * (max 1 A) ^ 6 / q ^ 3 := by
  classical
  calc
    _ ≤ ∑ n : Fin 7, (5 : ℝ) ^ n.val * ((max 1 A) ^ 6 / q ^ 3) := by
      apply Finset.sum_le_sum
      intro n _
      exact sum_schedule_bounds_le A q hA hq n.val (by omega)
    _ = _ := by rw [← Finset.sum_mul, schedule_count]; ring

theorem sum_masses_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (mass : (n : Fin 7) → (Fin n.val → Fin 5) → ℝ)
    (hmass : ∀ n s, 3 ≤ score s →
      mass n s ≤ A ^ n.val / q ^ score s) :
    (∑ n : Fin 7, ∑ s : Fin n.val → Fin 5,
      if 3 ≤ score s then mass n s else 0) ≤
        19531 * (max 1 A) ^ 6 / q ^ 3 := by
  classical
  apply le_trans _ (sum_all_schedule_bounds_le A q hA hq)
  apply Finset.sum_le_sum
  intro n _
  apply Finset.sum_le_sum
  intro s _
  split_ifs with hs
  · exact hmass n s hs
  · rfl

theorem sum_reweighted_costs_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q) :
    (∑ n : Fin 7, (5 * A) ^ n.val / q ^ 3) ≤
      19531 * (max 1 A) ^ 6 / q ^ 3 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  calc
    _ ≤ ∑ n : Fin 7, (5 : ℝ) ^ n.val * ((max 1 A) ^ 6 / q ^ 3) := by
      apply Finset.sum_le_sum
      intro n _
      have hnum : A ^ n.val ≤ (max 1 A) ^ 6 :=
        (pow_le_pow_left₀ hA (le_max_right _ _) _).trans
          (pow_le_pow_right₀ (le_max_left _ _) (by omega))
      rw [mul_pow, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hnum (le_of_lt (pow_pos hqpos _)))
        (by positivity)
    _ = _ := by rw [← Finset.sum_mul, schedule_count]; ring

theorem sum_length_masses_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (mass : Fin 7 → ℝ)
    (hmass : ∀ n, mass n ≤ (5 * A) ^ n.val / q ^ 3) :
    (∑ n : Fin 7, mass n) ≤ 19531 * (max 1 A) ^ 6 / q ^ 3 := by
  apply le_trans _ (sum_reweighted_costs_le A q hA hq)
  exact Finset.sum_le_sum (fun n _ => hmass n)

theorem aggregate_constant_pos (A : ℝ) : 0 < 19531 * (max 1 A) ^ 6 := by
  have : 0 < max 1 A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

end Balanced.ReuseSchedule

end OAI
