import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Finite extension of an arithmetic triple sum by zero -/

namespace JointDickman
open Finset

theorem finite_triple_sum_extend {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A A' : Finset α} {C C' : Finset β} (hA : A ⊆ A') (hC : C ⊆ C')
    (f : β → α → α → ℝ)
    (hsupp : ∀ c b a, f c b a ≠ 0 → c ∈ C ∧ b ∈ A ∧ a ∈ A) :
    (∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, f c b a) =
      ∑ c ∈ C', ∑ b ∈ A', ∑ a ∈ A', f c b a := by
  calc
    _ = ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A', f c b a := by
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro b _
      apply sum_subset hA
      intro a _ ha
      by_contra h
      exact ha (hsupp c b a h).2.2
    _ = ∑ c ∈ C, ∑ b ∈ A', ∑ a ∈ A', f c b a := by
      apply sum_congr rfl
      intro c _
      apply sum_subset hA
      intro b _ hb
      apply sum_eq_zero
      intro a _
      by_contra h
      exact hb (hsupp c b a h).2.1
    _ = _ := by
      apply sum_subset hC
      intro c _ hc
      apply sum_eq_zero
      intro b _
      apply sum_eq_zero
      intro a _
      by_contra h
      exact hc (hsupp c b a h).1

end JointDickman

end OAI
