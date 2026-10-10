import OAI.NumberTheory.Ostmann.Characters.SparseTensorModes

namespace OAI

/-! # The norm bound for the actual truncated tensor -/

namespace Ostmann
open scoped Classical BigOperators

theorem finiteKernelOperator_rectangular {α β : Type*} [Fintype α] [Fintype β]
    (c : ℕ → ℕ → α → β → ℂ) (N K : ℕ) :
    finiteKernelOperator (rectangularPolynomialSum c N K) =
      rectangularPolynomialSum (fun i j => finiteKernelOperator (c i j)) N K := by
  let L := (finiteKernelOperatorLinearMap :
    (α → β → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α))
  change L (rectangularPolynomialSum c N K) = _
  unfold rectangularPolynomialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_zero]
  rfl

theorem truncatedSparseTensorKernel_norm_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (K : ℕ) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    let H := ∑ i, (p i : ℝ)⁻¹
    ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
      U * Real.exp (-(8 / 5) * H) +
        2 * Real.exp (3 * H) * (100 / 103 : ℝ) ^ (K + 1) / (1 - 100 / 103) ^ 2 := by
  intro U H
  have hU : 0 < U := Finset.prod_pos (fun i _ =>
    (local_sparse_kernel_contraction (S i) (hS i) (hSp i) (hp i) (hlo i) (hhi i)
      ε hε hεsmall (hL1 i)).1)
  have hf : ‖finiteKernelOperator (sparseTensorKernel p S 1 1)‖ ≤
      U * Real.exp (-(8 / 5) * H) := by
    apply finiteKernelOperator_norm_le _ _ (mul_nonneg hU.le (Real.exp_pos _).le)
    exact sparseTensorKernel_contraction p S hS hSp hp hlo hhi ε hε hεsmall hL1
  have he := sparseTensorOperator_truncation_error p S hS hSp hp hlo hhi ε hε hεsmall hL1 K
  rw [← finiteKernelOperator_rectangular] at he
  change ‖finiteKernelOperator (sparseTensorKernel p S 1 1) -
    finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤ _ at he
  calc
    _ ≤ ‖finiteKernelOperator (sparseTensorKernel p S 1 1)‖ +
        ‖finiteKernelOperator (sparseTensorKernel p S 1 1) -
          finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ :=
      norm_le_insert _ _
    _ ≤ _ := add_le_add hf he

end Ostmann

end OAI
