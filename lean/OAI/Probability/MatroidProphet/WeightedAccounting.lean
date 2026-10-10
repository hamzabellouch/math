import OAI.Probability.MatroidProphet.Constants
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace MatroidProphet
open Finset

lemma sum_zpow_lt_upper (B : ℝ) (hB : 1 < B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i < l) :
    (∑ i ∈ s, B ^ i) < B ^ l / (B - 1) := by
  classical
  induction s using Finset.strongInductionOn generalizing l with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · let m := s.max' hs
      have hm : m ∈ s := s.max'_mem hs
      have hrest : ∀ i ∈ s.erase m, i < m := by
        intro i hi
        exact lt_of_le_of_ne (s.le_max' i (mem_of_mem_erase hi)) (ne_of_mem_erase hi)
      have hsum := ih (s.erase m) (erase_ssubset hm) m hrest
      have hml : m + 1 ≤ l := by have := hsl m hm; omega
      have hp : B ^ (m + 1) ≤ B ^ l := zpow_le_zpow_right₀ hB.le hml
      have hden : 0 < B - 1 := sub_pos.mpr hB
      have heq : B ^ m / (B - 1) + B ^ m = B ^ (m + 1) / (B - 1) := by
        rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))]
        field_simp
        ring
      calc
        (∑ i ∈ s, B ^ i) = (∑ i ∈ s.erase m, B ^ i) + B ^ m :=
          (sum_erase_add _ _ hm).symm
        _ < B ^ m / (B - 1) + B ^ m := by linarith
        _ = B ^ (m + 1) / (B - 1) := heq
        _ ≤ B ^ l / (B - 1) := div_le_div_of_nonneg_right hp hden.le
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      simp only [he, sum_empty]
      exact div_pos (zpow_pos (zero_lt_one.trans hB) _) (sub_pos.mpr hB)

lemma sum_zpow_le_two (B : ℝ) (hB : 2 ≤ B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i ≤ l) :
    (∑ i ∈ s, B ^ i) ≤ 2 * B ^ l := by
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  have hs := sum_zpow_lt_upper B hB1 s (l+1) (fun i hi => by have := hsl i hi; omega)
  have hp : 0 < B ^ l := zpow_pos (by linarith) _
  have hden : 0 < B - 1 := by linarith
  have hratio : B / (B - 1) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB1)), mul_div_assoc] at hs
  nlinarith

theorem higher_weight_cost (B : ℝ) (hB : 1 < B) (levels analyzed : Finset ℤ)
    (n : ℤ → ℝ) (hn : ∀ i ∈ levels, 0 ≤ n i) :
    (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, n l) ≤
      (∑ l ∈ levels, B ^ l * n l) / (B - 1) := by
  classical
  have heq : (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, n l) =
      ∑ l ∈ levels, (∑ i ∈ analyzed with i < l, B ^ i) * n l := by
    simp only [sum_filter, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  rw [heq, sum_div]
  apply sum_le_sum
  intro l hl
  have hs := sum_zpow_lt_upper B hB (analyzed.filter (· < l)) l
    (fun i hi => (mem_filter.mp hi).2)
  have hm := mul_le_mul_of_nonneg_right hs.le (hn l hl)
  simpa [div_mul_eq_mul_div] using hm

theorem cumulative_weight_bound {α : Type*} [DecidableEq α]
    (B : ℝ) (hB : 2 ≤ B) (A : Finset α) (level : α → ℤ) (analyzed : Finset ℤ) :
    (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => i ≤ level e)).card : ℝ)) ≤
      2 * ∑ e ∈ A, B ^ level e := by
  classical
  have heq : (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => i ≤ level e)).card : ℝ)) =
      ∑ e ∈ A, ∑ i ∈ analyzed with i ≤ level e, B ^ i := by
    simp_rw [sum_filter]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq, mul_sum]
  exact sum_le_sum fun e _ => sum_zpow_le_two B hB _ _
    (fun i hi => (mem_filter.mp hi).2)

end MatroidProphet

end OAI
