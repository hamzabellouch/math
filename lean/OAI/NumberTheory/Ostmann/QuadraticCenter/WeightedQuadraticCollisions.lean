import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPairCollision

namespace OAI

/-!
# Weighted coincidences of split quadratics

The two diagonal pairings contribute the squared second moment; every
other quadruple has at most one collision. This proves the counting
inequality underlying the character fourth moment in Section 6.
-/

namespace Ostmann

open scoped BigOperators

private theorem sum_four_weights {K : Type*} [Fintype K] (w : K → ℝ) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄) = (∑ b : K, w b) ^ 4 := by
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem sum_paired_weights {K : Type*} [Fintype K] [DecidableEq K]
    (w : K → ℝ) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄ *
        (if b₁ = b₃ ∧ b₂ = b₄ then 1 else 0)) = (∑ b : K, w b ^ 2) ^ 2 := by
  simp only [mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero]
  calc
    _ = ∑ b₁ : K, ∑ b₂ : K, w b₁ ^ 2 * w b₂ ^ 2 := by
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

private theorem sum_crossed_weights {K : Type*} [Fintype K] [DecidableEq K]
    (w : K → ℝ) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄ *
        (if b₁ = b₄ ∧ b₂ = b₃ then 1 else 0)) = (∑ b : K, w b ^ 2) ^ 2 := by
  simp only [mul_ite, mul_one, mul_zero, ite_and,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    _ = ∑ b₁ : K, ∑ b₂ : K, w b₁ ^ 2 * w b₂ ^ 2 := by
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- The weighted collision count is at most `2 |K| r² + J⁴`. -/
theorem weighted_quadratic_collisions_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (w : K → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄ *
        ((Finset.univ.filter (fun a : K =>
          (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ)) ≤
      2 * (Fintype.card K : ℝ) * (∑ b : K, w b ^ 2) ^ 2 + (∑ b : K, w b) ^ 4 := by
  calc
    _ ≤ ∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
        w b₁ * w b₂ * w b₃ * w b₄ *
          (1 + (Fintype.card K : ℝ) *
            ((if b₁ = b₃ ∧ b₂ = b₄ then 1 else 0) +
              (if b₁ = b₄ ∧ b₂ = b₃ then 1 else 0))) := by
      refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
        Finset.sum_le_sum fun b₃ _ => Finset.sum_le_sum fun b₄ _ => ?_
      exact mul_le_mul_of_nonneg_left (quadraticPair_collision_count_le b₁ b₂ b₃ b₄)
        (mul_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)) (hw _))
    _ = _ := by
      simp_rw [mul_add, mul_one]
      simp only [Finset.sum_add_distrib]
      have hpair := sum_paired_weights w
      have hcross := sum_crossed_weights w
      have hmass := sum_four_weights w
      simp_rw [← mul_assoc, mul_right_comm _ (Fintype.card K : ℝ)]
      simp only [← Finset.sum_mul]
      rw [hmass, hpair, hcross]
      ring

end Ostmann

end OAI
