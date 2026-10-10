import OAI.Combinatorics.ContingencyTables.Dense.DenseAffine
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace OAI

/-!
# Real completions with prescribed lower bounds

The dense geometric argument needs one strictly feasible normalized table.
Residual nonnegative real margins are completed by a rank-one table; this
is enough for the analytic interior-point argument and makes no algorithmic
claim about integral flow preprocessing.
-/

namespace ContingencyTables

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem real_table_exists (r : I → ℝ) (c : J → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j)
    (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ X : I → J → ℝ, (∀ i j, 0 ≤ X i j) ∧
      (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j) := by
  by_cases hzero : ∑ i, r i = 0
  · have hr₀ (i : I) : r i = 0 := by
      have h := Finset.single_le_sum (fun a _ => hr a) (Finset.mem_univ i)
      linarith [hr i]
    have hc₀ (j : J) : c j = 0 := by
      have h := Finset.single_le_sum (fun a _ => hc a) (Finset.mem_univ j)
      rw [← htotal, hzero] at h
      linarith [hc j]
    exact ⟨fun _ _ => 0, by simp, by simp [hr₀], by simp [hc₀]⟩
  · have hN : 0 < ∑ i, r i := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => hr i) (Ne.symm hzero)
    refine ⟨fun i j => r i * c j / (∑ i, r i), ?_, ?_, ?_⟩
    · intro i j
      exact div_nonneg (mul_nonneg (hr i) (hc j)) hN.le
    · intro i
      rw [← Finset.sum_div, ← Finset.mul_sum, ← htotal]
      field_simp
    · intro j
      rw [← Finset.sum_div, ← Finset.sum_mul]
      field_simp

theorem lower_bounded_real_table (r : I → ℝ) (c : J → ℝ) (lower : I → J → ℝ)
    (htotal : ∑ i, r i = ∑ j, c j)
    (hrow : ∀ i, ∑ j, lower i j ≤ r i) (hcol : ∀ j, ∑ i, lower i j ≤ c j) :
    ∃ X : I → J → ℝ, (∀ i j, lower i j ≤ X i j) ∧
      (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j) := by
  let r₀ : I → ℝ := fun i => r i - ∑ j, lower i j
  let c₀ : J → ℝ := fun j => c j - ∑ i, lower i j
  have ht : ∑ i, r₀ i = ∑ j, c₀ j := by
    simp only [r₀, c₀, Finset.sum_sub_distrib, htotal]
    rw [Finset.sum_comm (f := lower)]
  obtain ⟨Y, hY, hR, hC⟩ := real_table_exists r₀ c₀
    (fun i => sub_nonneg.mpr (hrow i)) (fun j => sub_nonneg.mpr (hcol j)) ht
  refine ⟨fun i j => lower i j + Y i j, ?_, ?_, ?_⟩
  · intro i j
    linarith [hY i j]
  · intro i
    rw [Finset.sum_add_distrib, hR]
    dsimp [r₀]
    ring
  · intro j
    rw [Finset.sum_add_distrib, hC]
    dsimp [c₀]
    ring

/-- Assigning `min(rᵢ,cⱼ)/(2d)` to every cell leaves nonnegative residual
margins whenever each dimension is at most `d`. -/
theorem strict_real_completion (r : I → ℝ) (c : J → ℝ) (d : ℝ)
    (hd : 0 < d) (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j)
    (hrows : (Fintype.card I : ℝ) ≤ d) (hcols : (Fintype.card J : ℝ) ≤ d)
    (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ X : I → J → ℝ, (∀ i j, min (r i) (c j) / (2 * d) ≤ X i j) ∧
      (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j) := by
  apply lower_bounded_real_table r c (fun i j => min (r i) (c j) / (2 * d)) htotal
  · intro i
    calc
      (∑ j, min (r i) (c j) / (2 * d)) ≤ ∑ _j : J, r i / (2 * d) := by
        apply Finset.sum_le_sum
        intro j _
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = Fintype.card J * (r i / (2 * d)) := by simp
      _ ≤ d * (r i / (2 * d)) := mul_le_mul_of_nonneg_right hcols
        (div_nonneg (hr i) (by positivity))
      _ ≤ r i := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show 0 < 2 * d by positivity)).mpr
        nlinarith [hr i]
  · intro j
    calc
      (∑ i, min (r i) (c j) / (2 * d)) ≤ ∑ _i : I, c j / (2 * d) := by
        apply Finset.sum_le_sum
        intro i _
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = Fintype.card I * (c j / (2 * d)) := by simp
      _ ≤ d * (c j / (2 * d)) := mul_le_mul_of_nonneg_right hrows
        (div_nonneg (hc j) (by positivity))
      _ ≤ c j := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show 0 < 2 * d by positivity)).mpr
        nlinarith [hc j]

end ContingencyTables

end OAI
