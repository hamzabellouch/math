import Mathlib

namespace OAI

namespace Problem355.Sampling

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sum_repeated_labels_le (f : α → α → α → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ a b c, f a b c ≤ M)
    (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a b c = 0) :
    (∑ a, ∑ b, ∑ c, f a b c) ≤ 3 * (Fintype.card α : ℝ) ^ 2 * M := by
  have hpoint (a b c : α) : f a b c ≤
      (if a = b then M else 0) + (if a = c then M else 0) +
        (if b = c then M else 0) := by
    have hf := hbound a b c
    by_cases hab : a = b
    · simp only [ite_eq_left hab]
      split_ifs <;> linarith
    by_cases hac : a = c
    · simp only [ite_eq_right hab, ite_eq_left hac, zero_add]
      split_ifs <;> linarith
    by_cases hbc : b = c
    · simp only [ite_eq_right hab, ite_eq_right hac, ite_eq_left hbc, zero_add]
      exact hf
    simp only [ite_eq_right hab, ite_eq_right hac, ite_eq_right hbc, add_zero,
      hzero a b c hab hac hbc, le_refl]
  calc
    (∑ a, ∑ b, ∑ c, f a b c) ≤
        ∑ a : α, ∑ b : α, ∑ c : α,
          ((if a = b then M else 0) + (if a = c then M else 0) +
            (if b = c then M else 0)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum fun c hc => hpoint a b c
    _ = 3 * (Fintype.card α : ℝ) ^ 2 * M := by
      simp only [Finset.sum_add_distrib]
      simp
      ring

theorem average_repeated_labels_le [Nonempty α]
    (f : α → α → α → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ a b c, f a b c ≤ M)
    (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a b c = 0) :
    (∑ a, ∑ b, ∑ c, f a b c) / (Fintype.card α : ℝ) ^ 3 ≤
      3 * M / (Fintype.card α : ℝ) := by
  have hcard : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (pow_pos hcard 3)).2
  calc
    (∑ a, ∑ b, ∑ c, f a b c) ≤
        3 * (Fintype.card α : ℝ) ^ 2 * M :=
      sum_repeated_labels_le f M hM hbound hzero
    _ = 3 * M / (Fintype.card α : ℝ) * (Fintype.card α : ℝ) ^ 3 := by
      field_simp

theorem card_repeated_labels_le :
    (Finset.univ.filter fun t : α × α × α =>
      t.1 = t.2.1 ∨ t.1 = t.2.2 ∨ t.2.1 = t.2.2).card ≤
        3 * Fintype.card α ^ 2 := by
  have h := sum_repeated_labels_le
    (fun a b c : α => if a = b ∨ a = c ∨ b = c then (1 : ℝ) else 0)
    1 (by norm_num)
    (by intro a b c; split_ifs <;> norm_num)
    (by intro a b c hab hac hbc; simp [hab, hac, hbc])
  have hid : ((Finset.univ.filter fun t : α × α × α =>
      t.1 = t.2.1 ∨ t.1 = t.2.2 ∨ t.2.1 = t.2.2).card : ℝ) =
      ∑ a : α, ∑ b : α, ∑ c : α,
        if a = b ∨ a = c ∨ b = c then (1 : ℝ) else 0 := by
    rw [← Finset.sum_boole]
    simp only [Fintype.sum_prod_type]
  rw [← hid] at h
  norm_num only [mul_one] at h
  exact_mod_cast h

theorem repeated_labels_probability_le [Nonempty α] :
    ((Finset.univ.filter fun t : α × α × α =>
      t.1 = t.2.1 ∨ t.1 = t.2.2 ∨ t.2.1 = t.2.2).card : ℝ) /
        (Fintype.card α : ℝ) ^ 3 ≤ 3 / (Fintype.card α : ℝ) := by
  have hcard : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (pow_pos hcard 3)).2
  calc
    ((Finset.univ.filter fun t : α × α × α =>
        t.1 = t.2.1 ∨ t.1 = t.2.2 ∨ t.2.1 = t.2.2).card : ℝ) ≤
        3 * (Fintype.card α : ℝ) ^ 2 := by
      exact_mod_cast (card_repeated_labels_le (α := α))
    _ = 3 / (Fintype.card α : ℝ) * (Fintype.card α : ℝ) ^ 3 := by
      field_simp

theorem conditional_collision_moment_le [Nonempty α]
    {Ω : Type*} [Fintype Ω]
    (weight D : α → α → α → Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmoment : ∀ a b c, (∑ ω, weight a b c ω * D a b c ω) ≤ M) :
    (∑ a, ∑ b, ∑ c, ∑ ω,
      weight a b c ω *
        (if a = b ∨ a = c ∨ b = c then D a b c ω else 0)) /
          (Fintype.card α : ℝ) ^ 3 ≤ 3 * M / (Fintype.card α : ℝ) := by
  apply average_repeated_labels_le _ M hM
  · intro a b c
    by_cases h : a = b ∨ a = c ∨ b = c
    · simpa only [ite_eq_left h] using hmoment a b c
    · simpa only [ite_eq_right h, mul_zero, Finset.sum_const_zero] using hM
  · intro a b c hab hac hbc
    simp [hab, hac, hbc]

end Problem355.Sampling

end OAI
