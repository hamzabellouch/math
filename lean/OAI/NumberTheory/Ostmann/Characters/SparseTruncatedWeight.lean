import OAI.NumberTheory.Ostmann.Characters.FiniteKernelPairing
import OAI.NumberTheory.Ostmann.Supply.ElementaryPolynomial

namespace OAI

/-! # The truncated tensor is the squared subset weight -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def tensorPointCoordinates {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (a : ∀ i, ZMod (p i))
    (x : ∀ i, Option (ZMod (p i))) : ℂ :=
  ∏ i, residuePointCoordinates (S i) (a i) (x i)

theorem sparseTensorCoefficient_point_pairing {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i, a i ∈ S i)
    (hb : ∀ i, b i ∈ Finset.univ \ S i)
    (j k : ℕ) (hj : j < n + 1) (hk : k < n + 1) :
    kernelPairingLinearMap (tensorPointCoordinates p S a)
      (tensorPointCoordinates p (fun i => Finset.univ \ S i) b)
      (sparseTensorCoefficient p S j k) =
        elementaryCoefficient (fun i => localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) j *
        elementaryCoefficient (fun i => localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) k := by
  apply finitePolynomial₂_coefficient_unique (N := n + 1) _ _ _ j k hj hk
  intro u v
  rw [← kernelPairing_polynomial, ← sparseTensorKernel_polynomial,
    elementaryCoefficient_product]
  change (∑ x, conj (∏ i, residuePointCoordinates (S i) (a i) (x i)) *
    ∑ y, sparseTensorKernel p S u v x y *
      ∏ i, residuePointCoordinates (Finset.univ \ S i) (b i) (y i)) = _
  rw [sparseTensorKernel_point_identity p S a b ha hb u v, Finset.prod_mul_distrib]

theorem truncatedSparseTensorKernel_point_pairing {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i, a i ∈ S i)
    (hb : ∀ i, b i ∈ Finset.univ \ S i) (K : ℕ) :
    kernelPairingLinearMap (tensorPointCoordinates p S a)
      (tensorPointCoordinates p (fun i => Finset.univ \ S i) b)
      (truncatedSparseTensorKernel p S K) =
        elementaryTruncation (fun i => localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) K ^ 2 := by
  unfold truncatedSparseTensorKernel
  rw [kernelPairing_rectangular]
  rw [← elementaryTruncation_square]
  unfold rectangularPolynomialSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : j ≤ K ∧ k ≤ K
  · simp only [h]
    exact sparseTensorCoefficient_point_pairing p S a b ha hb j k
      (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
  · simp only [h, ite_false]

end Ostmann

end OAI
