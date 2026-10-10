import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open scoped BigOperators
namespace DirectionalTransience.StoppedWindow

theorem sum_window_increments (s : ℕ → ℝ) (N m : ℕ) :
    (∑ i ∈ Finset.range N, (s (i+m)-s i)) =
      ∑ j ∈ Finset.range m, (s (N+j)-s j) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h₁ := Finset.sum_range_add s N m
  have h₂ := Finset.sum_range_add s m N
  simp only [Nat.add_comm m N] at h₂
  have hh : (∑ i ∈ Finset.range N, s (i+m)) = ∑ i ∈ Finset.range N, s (m+i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]
  rw [hh]
  linarith

theorem sum_window_increments_le (s : ℕ → ℝ) (N m : ℕ) (C : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hC : ∀ i, s i ≤ C) :
    (∑ i ∈ Finset.range N, (s (i+m)-s i)) ≤ (m:ℝ)*C := by
  rw [sum_window_increments]
  calc
    (∑ j ∈ Finset.range m, (s (N+j)-s j)) ≤ ∑ _j ∈ Finset.range m, C := by
      apply Finset.sum_le_sum
      intro j _
      linarith [hs j, hC (N+j)]
    _ = _ := by simp

end DirectionalTransience.StoppedWindow

end

end OAI
