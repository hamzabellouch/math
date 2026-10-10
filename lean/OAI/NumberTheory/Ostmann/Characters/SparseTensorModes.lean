import OAI.NumberTheory.Ostmann.Characters.SparseTensorPolynomial
import OAI.NumberTheory.Ostmann.Supply.BilinearCubeSupport

namespace OAI

/-! # Only low centered modes survive the rectangular truncation -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def centeredCoordinateSupport {n : ℕ} {p : Fin n → ℕ}
    (x : ∀ i, Option (ZMod (p i))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ none)

theorem localSparseCoefficient_constant {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (x y : Option (ZMod p)) :
    localSparseCoefficient S E (false, false) x y =
      if x = none ∧ y = none then 1 else 0 := by
  cases x <;> cases y <;>
    simp [localSparseCoefficient, sparseResidueMatrix, finiteBlockMatrix,
      polydiscSparseScalar, polydiscSparseSide, polydiscLowerLinearMap,
      residueLowerLinearMap]

/-- A coefficient of bidegree `(j,k)` vanishes on every output or input
coordinate with more than `j+k` centered factors. -/
theorem sparseTensorCoefficient_mode_support {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (j k : ℕ)
    (x y : ∀ i, Option (ZMod (p i)))
    (h : j + k < (centeredCoordinateSupport x).card ∨
      j + k < (centeredCoordinateSupport y).card) :
    sparseTensorCoefficient p S j k x y = 0 := by
  simp only [sparseTensorCoefficient, cubeCoefficient, Finset.sum_apply]
  change cubeCoefficient (fun t => ∏ i, localSparseCoefficient (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) (t i) (x i) (y i)) j k = 0
  rcases h with h | h
  · apply cubeCoefficient_eq_zero_of_many_coordinates
      (fun i b => localSparseCoefficient (S i)
        (largeTransformSpectrum (normalizedResidueTransform (S i))) b (x i) (y i))
      (centeredCoordinateSupport x) _ j k h
    intro i hi
    have hx : x i ≠ none := (Finset.mem_filter.mp hi).2
    rw [localSparseCoefficient_constant]
    simp [hx]
  · apply cubeCoefficient_eq_zero_of_many_coordinates
      (fun i b => localSparseCoefficient (S i)
        (largeTransformSpectrum (normalizedResidueTransform (S i))) b (x i) (y i))
      (centeredCoordinateSupport y) _ j k h
    intro i hi
    have hy : y i ≠ none := (Finset.mem_filter.mp hi).2
    rw [localSparseCoefficient_constant]
    simp [hy]

noncomputable def truncatedSparseTensorKernel {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) :=
  rectangularPolynomialSum (sparseTensorCoefficient p S) (n + 1) K

theorem truncatedSparseTensorKernel_mode_support {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (x y : ∀ i, Option (ZMod (p i)))
    (h : 2 * K < (centeredCoordinateSupport x).card ∨
      2 * K < (centeredCoordinateSupport y).card) :
    truncatedSparseTensorKernel p S K x y = 0 := by
  simp only [truncatedSparseTensorKernel, rectangularPolynomialSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : j ≤ K ∧ k ≤ K
  · simp only [hjk]
    apply sparseTensorCoefficient_mode_support p S j k x y
    rcases h with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · simp only [hjk, ite_false, Pi.zero_apply]

theorem truncatedSparseTensorKernel_projected {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (x y : ∀ i, Option (ZMod (p i))) :
    truncatedSparseTensorKernel p S K x y =
      if (centeredCoordinateSupport x).card ≤ 2 * K ∧
        (centeredCoordinateSupport y).card ≤ 2 * K then
        truncatedSparseTensorKernel p S K x y else 0 := by
  by_cases h : (centeredCoordinateSupport x).card ≤ 2 * K ∧
      (centeredCoordinateSupport y).card ≤ 2 * K
  · simp [h]
  · simp only [h, ite_false]
    apply truncatedSparseTensorKernel_mode_support
    omega

end Ostmann

end OAI
