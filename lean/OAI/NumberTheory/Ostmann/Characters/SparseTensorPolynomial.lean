import OAI.NumberTheory.Ostmann.Characters.SparseMatrixPolynomial
import OAI.NumberTheory.Ostmann.Characters.SparseTensorKernel
import OAI.NumberTheory.Ostmann.Supply.BilinearCube
import OAI.NumberTheory.Ostmann.Characters.FiniteKernelOperator

namespace OAI

/-! # Concrete coefficients of the sparse tensor polynomial -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def localSparseCoefficient {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (b : Bool × Bool) (x y : Option (ZMod p)) : ℂ :=
  match b with
  | (false, false) => sparseResidueMatrix S E 0 0 x y
  | (true, false) => sparseResidueMatrix S E 1 0 x y - sparseResidueMatrix S E 0 0 x y
  | (false, true) => sparseResidueMatrix S E 0 1 x y - sparseResidueMatrix S E 0 0 x y
  | (true, true) => sparseResidueMatrix S E 1 1 x y - sparseResidueMatrix S E 1 0 x y -
      sparseResidueMatrix S E 0 1 x y + sparseResidueMatrix S E 0 0 x y

noncomputable def sparseTensorCoefficient {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (j k : ℕ) :
    (∀ i, Option (ZMod (p i))) → (∀ i, Option (ZMod (p i))) → ℂ :=
  cubeCoefficient (fun t => fun x y => ∏ i, localSparseCoefficient (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) (t i) (x i) (y i)) j k

theorem sparseTensorKernel_polynomial {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    sparseTensorKernel p S u v = finitePolynomial₂ (sparseTensorCoefficient p S) (n + 1) u v := by
  funext x y
  have he := bilinear_product_expansion
    (fun i b => localSparseCoefficient (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) b (x i) (y i)) u v
  change (∏ i, sparseResidueMatrix (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) u v (x i) (y i)) = _
  have hl (i : Fin n) : sparseResidueMatrix (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) u v (x i) (y i) =
      localSparseCoefficient (S i) _ (false, false) (x i) (y i) +
      u * localSparseCoefficient (S i) _ (true, false) (x i) (y i) +
      v * localSparseCoefficient (S i) _ (false, true) (x i) (y i) +
      u * v * localSparseCoefficient (S i) _ (true, true) (x i) (y i) :=
    sparseResidueMatrix_polynomial (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) u v (x i) (y i)
  calc
    _ = _ := Finset.prod_congr rfl (fun i _ => hl i)
    _ = _ := by
      simpa only [sparseTensorCoefficient, finitePolynomial₂, finitePolynomial,
        cubeCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

theorem finiteKernelOperator_polynomial {α β : Type*} [Fintype α] [Fintype β]
    (c : ℕ → ℕ → α → β → ℂ) (N : ℕ) (u v : ℂ) :
    finiteKernelOperator (finitePolynomial₂ c N u v) =
      finitePolynomial₂ (fun i j => finiteKernelOperator (c i j)) N u v := by
  let L := (finiteKernelOperatorLinearMap :
    (α → β → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α))
  change L (finitePolynomial₂ c N u v) = _
  simp only [finitePolynomial₂, finitePolynomial, map_sum, map_smul]
  rfl

theorem sparseTensorOperator_polynomial {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    finiteKernelOperator (sparseTensorKernel p S u v) =
      finitePolynomial₂ (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
        (n + 1) u v := by
  rw [sparseTensorKernel_polynomial, finiteKernelOperator_polynomial]

/-- The actual coefficient truncation of the tensor has exponentially small error
in the cutoff, with the exact radius `1.03` from the local estimate. -/
theorem sparseTensorOperator_truncation_error {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (K : ℕ) :
    ‖finiteKernelOperator (sparseTensorKernel p S 1 1) -
      rectangularPolynomialSum (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
        (n + 1) K‖ ≤
      2 * Real.exp (3 * ∑ i, (p i : ℝ)⁻¹) * (100 / 103 : ℝ) ^ (K + 1) /
        (1 - 100 / 103) ^ 2 := by
  rw [sparseTensorOperator_polynomial]
  have hbound (u v : ℂ) (hu : ‖u‖ = 103 / 100) (hv : ‖v‖ = 103 / 100) :
      ‖finitePolynomial₂ (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
        (n + 1) u v‖ ≤ Real.exp (3 * ∑ i, (p i : ℝ)⁻¹) := by
    rw [← sparseTensorOperator_polynomial]
    apply finiteKernelOperator_norm_le _ _ (Real.exp_pos _).le
    exact sparseTensorKernel_energy_le p S hS hSp hp hlo hhi ε hε hεsmall hL1 u v hu.le hv.le
  have ht := finitePolynomial₂_truncation_error
    (fun i j => finiteKernelOperator (sparseTensorCoefficient p S i j))
    (103 / 100) _ (by norm_num) (Real.exp_pos _).le hbound K
  simpa only [show (103 / 100 : ℝ)⁻¹ = 100 / 103 by norm_num] using ht

end Ostmann

end OAI
