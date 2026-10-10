import Mathlib
import OAI.Combinatorics.KMedian.PCP.FiniteTest

namespace OAI

section Inline_PCPTestSum

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

noncomputable def testSum {S : Type} [Fintype S] (p : S → Prop) : ℝ :=
  ∑ s, if p s then 1 else 0

lemma testSum_nonneg {S : Type} [Fintype S] (p : S → Prop) : 0 ≤ testSum p :=
  sum_nonneg (by intro s _; split_ifs <;> norm_num)

lemma testSum_congr {S : Type} [Fintype S] {p q : S → Prop} (h : ∀ s, p s ↔ q s) :
    testSum p=testSum q := by
  unfold testSum
  apply sum_congr rfl
  intro s _
  simp only [h s]

lemma testSum_mono {S : Type} [Fintype S] {p q : S → Prop} (h : ∀ s, p s → q s) :
    testSum p≤testSum q := by
  unfold testSum
  apply sum_le_sum
  intro s _
  by_cases hp : p s
  · simp [hp,h s hp]
  · simp only [ite_eq_right hp]; split_ifs <;> norm_num

lemma testSum_card_rate {S : Type} [Fintype S] [Nonempty S] (p : S → Prop) :
    testSum p=Fintype.card S*testRate p := by
  unfold testSum testRate
  rw [Fintype.expect_eq_sum_div_card]
  have hn : (Fintype.card S:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma testSum_union_bound {S : Type} [Fintype S] {p q r : S → Prop}
    (h : ∀ s, p s → q s ∨ r s) : testSum p≤testSum q+testSum r := by
  unfold testSum
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro s _
  by_cases hp : p s
  · obtain hq|hr := h s hp
    · simp [hp,hq]; split_ifs <;> norm_num
    · simp [hp,hr]; split_ifs <;> norm_num
  · simp only [ite_eq_right hp]; split_ifs <;> norm_num

lemma testSum_injection {S T : Type} [Fintype S] [Fintype T] (e : S ↪ T)
    {p : S → Prop} {q : T → Prop} (h : ∀ s, p s → q (e s)) : testSum p≤testSum q := by
  calc
    testSum p ≤ testSum (fun s => q (e s)) := testSum_mono h
    _ = ∑ t ∈ univ.map e, if q t then (1:ℝ) else 0 := by
      unfold testSum
      rw [sum_map]
    _ ≤ testSum q := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro t _ _
      split_ifs <;> norm_num

lemma testSum_prod {S T : Type} [Fintype S] [Fintype T] (p : S × T → Prop) :
    testSum p=∑ s, testSum (fun t => p (s,t)) := by
  exact Fintype.sum_prod_type _

lemma testSum_sigma {S : Type} {T : S → Type} [Fintype S] [∀ s,Fintype (T s)]
    (p : ((s : S) × T s) → Prop) : testSum p=∑ s, testSum (fun t => p ⟨s,t⟩) := by
  exact Fintype.sum_sigma _

end MetricKMedian.PCP

end Inline_PCPTestSum

end OAI
