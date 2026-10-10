import OAI.Probability.SignedSweeps.WordSpecht

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

def wordIntertwiner {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C) :
    Representation.IntertwiningMap (wordRepresentation p C) (wordRepresentation p C) :=
  (wordCommutantEquiv p C).symm ⟨A, hA⟩

@[simp] lemma wordIntertwiner_matrix {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C) :
    wordMatrixEquiv p C (wordIntertwiner A hA).toLinearMap = A :=
  (wordMatrixEquiv p C).apply_symm_apply A

def wordTensorOrbitHull (p : ℕ) (C : Type*) [Fintype C] (A : Matrix C C ℂ) :
    Set (MatrixHilbert (Fin p → C)) :=
  closedOrbitHull (matrixConjugationAction (I := Fin p → C) (wordUnitaryHom p C))
    (matrixHilbertEquiv (wordTensorMatrix p A))

theorem exists_word_scalar_twirl {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C) (A : Matrix C C ℂ) :
    ∃ B : Matrix (Fin p → C) (Fin p → C) ℂ,
      matrixHilbertEquiv B ∈ wordTensorOrbitHull p C A ∧
      B ∈ wordCommutant p C ∧
      ∃ z : ℂ, ∀ x ∈ (isotypicSubrepresentation (spechtRepresentation μ)
          (wordRepresentation p C)).toSubmodule,
        (wordMatrixEquiv p C).symm B x = z • x := by
  let ρ := spechtRepresentation μ
  let σ := wordRepresentation p C
  let f := spechtOrbitIntertwiner μ σ (EuclideanSpace.single (rowColorWord μ color) 1)
  have hf : f ≠ 0 := by
    intro h
    have hz : f (spechtGenerator μ) = f 0 := by rw [h]; rfl
    exact spechtGenerator_ne_zero μ (specht_occurs_word μ color hz)
  let := specht_irreducible μ
  obtain ⟨j, hj⟩ := intertwiner_isometric_normalization ρ σ
    (spechtRepresentation_norm μ) wordRepresentation_norm f hf
  obtain ⟨B, hB, hcomm⟩ := exists_matrix_twirl (wordUnitaryHom p C) (wordTensorMatrix p A)
  have hmem : B ∈ wordCommutant p C := by
    apply matrix_twirl_submodule (wordUnitaryHom p C) hB
    intro U
    change wordTensorMatrix p U.1 * wordTensorMatrix p A *
      star (wordTensorMatrix p U.1) ∈ _
    rw [Matrix.star_eq_conjTranspose, ← wordTensorMatrix_star]
    exact wordCommutant_mul (wordCommutant_mul (wordTensor_mem_commutant _)
      (wordTensor_mem_commutant _)) (wordTensor_mem_commutant _)
  let T := wordIntertwiner B hmem
  have hc (D : Representation.IntertwiningMap σ σ) : T.comp D = D.comp T := by
    apply Representation.IntertwiningMap.ext
    apply (wordMatrixEquiv p C).injective
    change wordMatrixEquiv p C (T.toLinearMap * D.toLinearMap) =
      wordMatrixEquiv p C (D.toLinearMap * T.toLinearMap)
    simp only [map_mul, wordIntertwiner_matrix, T]
    exact wordUnitary_central B hcomm _
      ((wordMatrix_intertwining _).mp ⟨D.isIntertwining _ _⟩)
  obtain ⟨z, hz⟩ := central_scalar_on_isotypic ρ σ
    (spechtRepresentation_norm μ) wordRepresentation_norm j hj T hc
  exact ⟨B, hB, hmem, z, hz⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma trace_starProjection (S : Submodule ℂ F) :
    LinearMap.trace ℂ F S.starProjection.toLinearMap = (finrank ℂ S : ℂ) := by
  change LinearMap.trace ℂ F (S.subtype ∘ₗ S.orthogonalProjectionOnto.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  have he : S.orthogonalProjectionOnto.toLinearMap ∘ₗ S.subtype = LinearMap.id := by
    ext x
    simp
  rw [he, LinearMap.trace_id]

lemma trace_scalar_projection (S : Submodule ℂ F) (T : F →ₗ[ℂ] F) (z : ℂ)
    (hT : ∀ x ∈ S, T x = z • x) :
    LinearMap.trace ℂ F (T * S.starProjection.toLinearMap) = z * (finrank ℂ S : ℂ) := by
  have he : T * S.starProjection.toLinearMap = z • S.starProjection.toLinearMap := by
    ext x
    exact hT _ (S.starProjection_apply_mem x)
  rw [he, map_smul, trace_starProjection, smul_eq_mul]

lemma positive_trace_isometric_copy (T : F →ₗ[ℂ] F) (hT : T.IsPositive)
    (j : E →ₗᵢ[ℂ] F) (z : ℂ) (hj : ∀ x, T (j x) = z • j x) :
    z.re * (finrank ℂ E : ℝ) ≤ (LinearMap.trace ℂ F T).re := by
  let b := stdOrthonormalBasis ℂ E
  have ho : Orthonormal ℂ (fun i => j (b i)) := by
    rw [orthonormal_iff_ite]
    intro i k
    rw [j.inner_map_map, b.inner_eq_ite]
  have ht := positive_orthonormal_trace_le T hT (fun i => j (b i)) ho
  have hi (i : Fin (finrank ℂ E)) : (inner ℂ (j (b i)) (T (j (b i)))).re = z.re := by
    rw [hj, inner_smul_right, j.inner_map_map, b.inner_eq_ite]
    simp
  simpa only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    using ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma wordMatrix_trace {p : ℕ} {C : Type*} [Fintype C]
    (T : WordSpace p C →ₗ[ℂ] WordSpace p C) :
    Matrix.trace (wordMatrixEquiv p C T) = LinearMap.trace ℂ (WordSpace p C) T :=
  (LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin p → C) ℂ).toBasis T).symm

lemma wordMatrix_projection_commute {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hA : A ∈ wordCommutant p C) :
    wordMatrixEquiv p C (isotypicSubrepresentation (spechtRepresentation μ)
        (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap * A =
      A * wordMatrixEquiv p C (isotypicSubrepresentation (spechtRepresentation μ)
        (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap := by
  have h := isotypic_projection_commute (spechtRepresentation μ) (wordRepresentation p C)
    wordRepresentation_norm (wordIntertwiner A hA)
  have he := congrArg (wordMatrixEquiv p C) h
  simpa only [map_mul, wordIntertwiner_matrix] using he

end SignedSweeps
end

end OAI
