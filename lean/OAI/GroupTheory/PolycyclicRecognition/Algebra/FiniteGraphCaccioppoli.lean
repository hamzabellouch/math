import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! # The finite-sum reverse energy estimate

The weights will be the adjacency indicators on a finite Cayley ball. The
cutoff is supported where the original function is harmonic.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {I : Type*} [Fintype I]

def weightedEdgeSum (w : I → I → ℝ) (F : I → I → ℝ) : ℝ :=
  ∑ x, ∑ y, w x y * F x y

theorem weightedEdgeSum_swap (w : I → I → ℝ) (hw : ∀ x y, w x y = w y x)
    (F : I → I → ℝ) : weightedEdgeSum w F = weightedEdgeSum w (fun x y => F y x) := by
  unfold weightedEdgeSum
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [hw y x]

theorem finite_graph_green_identity (w : I → I → ℝ) (hw : ∀ x y, w x y = w y x)
    (f φ : I → ℝ) :
    weightedEdgeSum w (fun x y => (f y - f x) * (φ y - φ x)) =
      -2 * ∑ x, φ x * ∑ y, w x y * (f y - f x) := by
  have hs : weightedEdgeSum w (fun x y => (f y - f x) * φ y) =
      -weightedEdgeSum w (fun x y => (f y - f x) * φ x) := by
    rw [weightedEdgeSum_swap w hw]
    unfold weightedEdgeSum
    simp only [← sum_neg_distrib]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    ring
  have he : weightedEdgeSum w (fun x y => (f y - f x) * (φ y - φ x)) =
      weightedEdgeSum w (fun x y => (f y - f x) * φ y) -
        weightedEdgeSum w (fun x y => (f y - f x) * φ x) := by
    simp only [weightedEdgeSum, mul_sub, sum_sub_distrib]
  rw [he, hs]
  have hp : weightedEdgeSum w (fun x y => (f y - f x) * φ x) =
      ∑ x, φ x * ∑ y, w x y * (f y - f x) := by
    unfold weightedEdgeSum
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro y _
    ring
  rw [hp]
  ring

theorem finite_graph_caccioppoli
    (w : I → I → ℝ) (hw : ∀ x y, w x y = w y x) (hpos : ∀ x y, 0 ≤ w x y)
    (f η : I → ℝ)
    (hharm : ∀ x, η x ≠ 0 → ∑ y, w x y * (f y - f x) = 0) :
    weightedEdgeSum w (fun x y => η x ^ 2 * (f y - f x) ^ 2) ≤
      4 * weightedEdgeSum w (fun x y => f x ^ 2 * (η y - η x) ^ 2) := by
  let P := weightedEdgeSum w (fun x y => (η y * f y - η x * f x) ^ 2)
  let C := weightedEdgeSum w (fun x y => f x * f y * (η y - η x) ^ 2)
  let E := weightedEdgeSum w (fun x y => f x ^ 2 * (η y - η x) ^ 2)
  have hz : weightedEdgeSum w
      (fun x y => (f y - f x) * (η y ^ 2 * f y - η x ^ 2 * f x)) = 0 := by
    rw [finite_graph_green_identity w hw]
    have he : ∑ x, (η x ^ 2 * f x) * ∑ y, w x y * (f y - f x) = 0 := by
      apply sum_eq_zero
      intro x _
      by_cases hx : η x = 0
      · simp only [hx, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
      · rw [hharm x hx, mul_zero]
    rw [he, mul_zero]
  have hPC : P = C := by
    have he : P - C = weightedEdgeSum w
        (fun x y => (f y - f x) * (η y ^ 2 * f y - η x ^ 2 * f x)) := by
      dsimp only [P, C, weightedEdgeSum]
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro x _
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro y _
      ring
    linarith
  have hswap : weightedEdgeSum w (fun x y => f y ^ 2 * (η y - η x) ^ 2) = E := by
    rw [weightedEdgeSum_swap w hw]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    dsimp
    ring
  have hCE : C ≤ E := by
    have he : 2 * C ≤ E + weightedEdgeSum w (fun x y => f y ^ 2 * (η y - η x) ^ 2) := by
      dsimp only [C, E, weightedEdgeSum]
      rw [mul_sum, ← sum_add_distrib]
      apply sum_le_sum
      intro x _
      rw [mul_sum, ← sum_add_distrib]
      apply sum_le_sum
      intro y _
      have hxy : 2 * (f x * f y) ≤ f x ^ 2 + f y ^ 2 := by
        nlinarith [sq_nonneg (f x - f y)]
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hxy (sq_nonneg (η y - η x))) (hpos x y)
      nlinarith only [hh]
    rw [hswap] at he
    linarith
  have hbound : weightedEdgeSum w (fun x y => η x ^ 2 * (f y - f x) ^ 2) ≤
      2 * P + 2 * weightedEdgeSum w (fun x y => f y ^ 2 * (η y - η x) ^ 2) := by
    dsimp only [weightedEdgeSum, P]
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro x _
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro y _
    have hs := sq_nonneg ((η y * f y - η x * f x) + f y * (η y - η x))
    have hp : η x ^ 2 * (f y - f x) ^ 2 ≤
        2 * (η y * f y - η x * f x) ^ 2 + 2 * (f y ^ 2 * (η y - η x) ^ 2) := by
      nlinarith only [hs]
    have hh := mul_le_mul_of_nonneg_left hp (hpos x y)
    nlinarith only [hh]
  rw [hswap, hPC] at hbound
  dsimp only [E] at hCE hbound
  linarith

end PolycyclicRecognition

end

end OAI
