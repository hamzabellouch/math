import Mathlib.Analysis.Normed.Module.FiniteDimension
import OAI.NumberTheory.Ostmann.Supply.FiniteTensorKernel

namespace OAI

/-! # The counting-energy matrix as a continuous operator -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators

noncomputable def finiteKernelOperator {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem finiteKernelOperator_apply {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) (f : EuclideanSpace ℂ β) (x : α) :
    finiteKernelOperator M f x = ∑ y, M x y * f y := rfl

theorem finiteKernelOperator_norm_le {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ f : β → ℂ, (∑ x, ‖∑ y, M x y * f y‖ ^ 2) ≤ B ^ 2 * ∑ y, ‖f y‖ ^ 2) :
    ‖finiteKernelOperator M‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg f))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa only [finiteKernelOperator_apply] using hM (fun y => f y)

theorem finiteKernelOperator_add {α β : Type*} [Fintype α] [Fintype β]
    (M N : α → β → ℂ) :
    finiteKernelOperator (fun x y => M x y + N x y) = finiteKernelOperator M + finiteKernelOperator N := by
  ext f x
  change (∑ y, (M x y + N x y) * f y) =
    (finiteKernelOperator M f) x + (finiteKernelOperator N f) x
  simp only [finiteKernelOperator_apply, add_mul, Finset.sum_add_distrib]

theorem finiteKernelOperator_smul {α β : Type*} [Fintype α] [Fintype β]
    (a : ℂ) (M : α → β → ℂ) :
    finiteKernelOperator (fun x y => a * M x y) = a • finiteKernelOperator M := by
  ext f x
  change (∑ y, (a * M x y) * f y) = a * (finiteKernelOperator M f) x
  simp only [finiteKernelOperator_apply, Finset.mul_sum, mul_assoc]

noncomputable def finiteKernelOperatorLinearMap {α β : Type*} [Fintype α] [Fintype β] :
    (α → β → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α) where
  toFun := finiteKernelOperator
  map_add' M N := finiteKernelOperator_add M N
  map_smul' a M := finiteKernelOperator_smul a M

end Ostmann

end OAI
