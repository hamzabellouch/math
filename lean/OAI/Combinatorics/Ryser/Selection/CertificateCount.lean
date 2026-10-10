import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Selection

open scoped BigOperators

variable {α : Type*} [instDecidableEqα : DecidableEq α]

theorem sum_powerset_pow_card_le_exp (S : Finset α) (x : ℝ) (hx : 0 ≤ x) :
    (∑ T ∈ S.powerset, x ^ T.card) ≤ Real.exp ((S.card : ℝ) * x) := let _ := instDecidableEqα; by
  calc
    (∑ T ∈ S.powerset, x ^ T.card) = ∏ _a ∈ S, (1 + x) := by
      simpa only [Finset.prod_const] using
        (Finset.prod_one_add (f := fun _ : α => x) S).symm
    _ ≤ Real.exp (∑ _a ∈ S, x) :=
      Real.prod_one_add_le_exp_sum S (fun _ => hx)
    _ = Real.exp ((S.card : ℝ) * x) := by simp

theorem card_small_subsets_mul_pow_le_exp (S : Finset α) (r : ℕ)
    (x : ℝ) (hx : 0 ≤ x) (hx_one : x ≤ 1) :
    (((S.powerset.filter (fun T => T.card ≤ r)).card : ℝ) * x ^ r) ≤
      Real.exp ((S.card : ℝ) * x) := by
  calc
    (((S.powerset.filter (fun T => T.card ≤ r)).card : ℝ) * x ^ r) =
        ∑ _T ∈ S.powerset.filter (fun T => T.card ≤ r), x ^ r := by simp
    _ ≤ ∑ T ∈ S.powerset.filter (fun T => T.card ≤ r), x ^ T.card := by
      apply Finset.sum_le_sum
      intro T hT
      exact pow_le_pow_of_le_one hx hx_one (Finset.mem_filter.mp hT).2
    _ ≤ ∑ T ∈ S.powerset, x ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun T _ _ => pow_nonneg hx T.card)
    _ ≤ Real.exp ((S.card : ℝ) * x) := sum_powerset_pow_card_le_exp S x hx

theorem card_fixed_subsets_mul_pow_le_exp (S : Finset α) (m : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (((S.powerset.filter (fun T => T.card = m)).card : ℝ) * x ^ m) ≤
      Real.exp ((S.card : ℝ) * x) := by
  calc
    (((S.powerset.filter (fun T => T.card = m)).card : ℝ) * x ^ m) =
        ∑ _T ∈ S.powerset.filter (fun T => T.card = m), x ^ m := by simp
    _ = ∑ T ∈ S.powerset.filter (fun T => T.card = m), x ^ T.card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [(Finset.mem_filter.mp hT).2]
    _ ≤ ∑ T ∈ S.powerset, x ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun T _ _ => pow_nonneg hx T.card)
    _ ≤ Real.exp ((S.card : ℝ) * x) := sum_powerset_pow_card_le_exp S x hx

theorem card_small_subsets_le (S : Finset α) (K m : ℕ)
    (hK : 1 ≤ K) (hcard : S.card = K * m) :
    ((S.powerset.filter (fun T => T.card ≤ 2 * m)).card : ℝ) ≤
      (3 * (K : ℝ) ^ 2) ^ m := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact Nat.one_le_cast.mpr hK
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hKr
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have he_three : Real.exp 1 ≤ (3 : ℝ) := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 : ℝ)) zero_le_one one_lt_two
    norm_num at h
    exact h
  have hweight := card_small_subsets_mul_pow_le_exp S (2 * m) (K : ℝ)⁻¹
    (inv_nonneg.mpr hKpos.le) (inv_le_one_of_one_le₀ hKr)
  have hexponent : (S.card : ℝ) * (K : ℝ)⁻¹ = (m : ℝ) := by
    rw [hcard, Nat.cast_mul]
    field_simp [hKne]
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) m
  have hcancel :
      (3 * (K : ℝ) ^ 2) ^ m * ((K : ℝ)⁻¹) ^ (2 * m) = (3 : ℝ) ^ m := by
    rw [pow_mul, ← mul_pow]
    congr 1
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hKne, one_pow, mul_one]
  apply (mul_le_mul_iff_left₀ (pow_pos (inv_pos.mpr hKpos) (2 * m))).mp
  calc
    ((S.powerset.filter (fun T => T.card ≤ 2 * m)).card : ℝ) *
        ((K : ℝ)⁻¹) ^ (2 * m) ≤ Real.exp (m : ℝ) := by
      simpa only [hexponent] using hweight
    _ = Real.exp 1 ^ m := hexp
    _ ≤ (3 : ℝ) ^ m :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he_three m
    _ = (3 * (K : ℝ) ^ 2) ^ m * ((K : ℝ)⁻¹) ^ (2 * m) := hcancel.symm

theorem card_fixed_subsets_le (S : Finset α) (m : ℕ) :
    ((S.powerset.filter (fun T => T.card = m)).card : ℝ) ≤
      (Real.exp 1 * (S.card : ℝ) / (m : ℝ)) ^ m := by
  by_cases hm : m = 0
  · subst m
    have hempty : S.powerset.filter (fun T => T.card = 0) = {∅} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero,
        Finset.mem_singleton]
      constructor
      · exact And.right
      · intro hT
        subst T
        exact ⟨Finset.empty_subset S, rfl⟩
    rw [hempty]
    simp
  by_cases hS : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [hm, Ne.symm hm]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hSne : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
  have hxpos : (0 : ℝ) < (m : ℝ) / (S.card : ℝ) := div_pos hmpos hSpos
  have hweight := card_fixed_subsets_mul_pow_le_exp S m
    ((m : ℝ) / (S.card : ℝ)) hxpos.le
  have hexponent :
      (S.card : ℝ) * ((m : ℝ) / (S.card : ℝ)) = (m : ℝ) := by
    field_simp [hmne, hSne]
  have hexp : Real.exp (m : ℝ) = Real.exp 1 ^ m := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) m
  have hcancel :
      (Real.exp 1 * (S.card : ℝ) / (m : ℝ)) ^ m *
          ((m : ℝ) / (S.card : ℝ)) ^ m = Real.exp 1 ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp [hmne, hSne]
  apply (mul_le_mul_iff_left₀ (pow_pos hxpos m)).mp
  calc
    ((S.powerset.filter (fun T => T.card = m)).card : ℝ) *
        ((m : ℝ) / (S.card : ℝ)) ^ m ≤ Real.exp (m : ℝ) := by
      simpa only [hexponent] using hweight
    _ = Real.exp 1 ^ m := hexp
    _ = (Real.exp 1 * (S.card : ℝ) / (m : ℝ)) ^ m *
        ((m : ℝ) / (S.card : ℝ)) ^ m := hcancel.symm

end RyserCoveringCounterexample.Selection

end OAI
