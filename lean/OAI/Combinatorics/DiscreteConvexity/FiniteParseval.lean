import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Finite Parseval identities from a weighted kernel

The algebraic statement below separates finite-sum rearrangement from the
concrete kernel identity. Neither the expansion nor the Parseval identity
requires nonnegative weights.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Expanding a weighted product of transforms gives the associated kernel. -/
theorem weighted_transform_bilinear_expansion
    (K : I → J → ℝ) (r : I → ℝ) (f g : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) * (∑ y, g y * K u y)) =
      ∑ x, ∑ y, f x * g y * (∑ u, r u * K u x * K u y) := by
  calc
    _ = ∑ u, ∑ x, ∑ y, f x * g y * (r u * K u x * K u y) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc, Fintype.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ x, ∑ y, ∑ u, f x * g y * (r u * K u x * K u y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, f x * g y * (∑ u, r u * K u x * K u y) := by
      simp only [Finset.mul_sum]

variable [DecidableEq J]

/-- A diagonal weighted kernel preserves the corresponding bilinear form. -/
theorem weighted_kernel_bilinear
    (K : I → J → ℝ) (r : I → ℝ) (μ : J → ℝ)
    (hkernel : ∀ x y, (∑ u, r u * K u x * K u y) =
      if x = y then μ x else 0) (f g : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) * (∑ y, g y * K u y)) =
      ∑ x, μ x * f x * g x := by
  rw [weighted_transform_bilinear_expansion]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [hkernel]
  calc
    (∑ y, f x * g y * (if x = y then μ x else 0)) =
        f x * g x * (if x = x then μ x else 0) := by
      apply Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
      intro y _ hy
      rw [ite_eq_right (Ne.symm hy), mul_zero]
    _ = μ x * f x * g x := by
      rw [ite_eq_left rfl]
      ring

/-- Finite Parseval follows from the weighted kernel identity. -/
theorem weighted_kernel_parseval
    (K : I → J → ℝ) (r : I → ℝ) (μ : J → ℝ)
    (hkernel : ∀ x y, (∑ u, r u * K u x * K u y) =
      if x = y then μ x else 0) (f : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) ^ 2) =
      ∑ x, μ x * (f x) ^ 2 := by
  simpa only [pow_two, mul_assoc] using weighted_kernel_bilinear K r μ hkernel f f

end TalagrandDiscreteConvexity

end OAI
