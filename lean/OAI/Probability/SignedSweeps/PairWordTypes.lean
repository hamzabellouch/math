import OAI.Probability.SignedSweeps.PositiveRootTensor
import OAI.Probability.SignedSweeps.WordDensity
import OAI.Probability.SignedSweeps.WordBlocks

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma hilbertBlock_intertwine (j : E →ₗᵢ[ℂ] F) (L : F →ₗ[ℂ] F)
    (A P : E →ₗ[ℂ] E) (hL : L ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ A)
    (hL' : L.adjoint ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ A.adjoint)
    (hAP : A * P = P * A) : L * hilbertBlock j P = hilbertBlock j P * L := by
  have hR := congrArg LinearMap.adjoint hL'
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] at hR
  ext x
  change L (j (P (j.toLinearMap.adjoint x))) = j (P (j.toLinearMap.adjoint (L x)))
  rw [show L (j (P (j.toLinearMap.adjoint x))) = j (A (P (j.toLinearMap.adjoint x))) from
    LinearMap.congr_fun hL _, show j.toLinearMap.adjoint (L x) = A (j.toLinearMap.adjoint x) from
    LinearMap.congr_fun hR x]
  exact congrArg j (LinearMap.congr_fun hAP _)

lemma starProjection_positive (S : Submodule ℂ E) :
    S.starProjection.toLinearMap.IsPositive := by
  let P := S.starProjection.toLinearMap
  have hP : P.IsSymmetric := S.starProjection_isSymmetric
  have hPP : P * P = P := congrArg ContinuousLinearMap.toLinearMap
    S.isIdempotentElem_starProjection.eq
  refine ⟨hP, ?_⟩
  intro x
  have he := projection_inner_eq P hP hPP x
  change 0 ≤ (inner ℂ (P x) x).re
  rw [show (inner ℂ (P x) x).re = (inner ℂ x (P x)).re from
    inner_re_symm (𝕜 := ℂ) _ _, he]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def wordTypeProjection {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    WordSpace p C →ₗ[ℂ] WordSpace p C :=
  (isotypicSubrepresentation (spechtRepresentation μ)
    (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap

lemma wordTypeProjection_positive {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    (wordTypeProjection μ C).IsPositive := starProjection_positive _

lemma wordTypeProjection_idempotent {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    wordTypeProjection μ C * wordTypeProjection μ C = wordTypeProjection μ C :=
  congrArg ContinuousLinearMap.toLinearMap
    (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).toSubmodule.isIdempotentElem_starProjection.eq

lemma wordTypeProjection_norm_le {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C]
    (x : WordSpace p C) : ‖wordTypeProjection μ C x‖ ≤ ‖x‖ :=
  Submodule.norm_starProjection_apply_le _ x

lemma wordTypeProjection_tensor_commute {p : ℕ} (μ : Partition p)
    {C : Type*} [Fintype C] (A : Matrix C C ℂ) :
    wordTypeProjection μ C * (wordTensorMatrix p A).toEuclideanLin =
      (wordTensorMatrix p A).toEuclideanLin * wordTypeProjection μ C := by
  have h := wordMatrix_projection_commute μ _ (wordTensor_mem_commutant A)
  apply (wordMatrixEquiv p C).injective
  change wordMatrixEquiv p C (wordTypeProjection μ C * (wordTensorMatrix p A).toEuclideanLin) =
    wordMatrixEquiv p C ((wordTensorMatrix p A).toEuclideanLin * wordTypeProjection μ C)
  have he := wordMatrixEquiv_symm (wordTensorMatrix p A)
  rw [← he]
  simpa only [map_mul, StarAlgEquiv.apply_symm_apply, wordTypeProjection] using h

def pairTypeProjection {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C] :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  ∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S))
    (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C))

lemma pairTypeProjection_positive {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C] :
    (pairTypeProjection h α β C).IsPositive := by
  apply LinearMap.isPositive_sum
  intro S _
  exact hilbertBlock_positive _ (tensor_map_positive _ _ (wordTypeProjection_positive α C)
    (wordTypeProjection_positive β C))

lemma pairTypeProjection_idempotent {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C] :
    pairTypeProjection h α β C * pairTypeProjection h α β C =
      pairTypeProjection h α β C := by
  let P := TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)
  have hPP : P * P = P := by
    rw [← TensorProduct.map_mul, wordTypeProjection_idempotent, wordTypeProjection_idempotent]
  change (∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (allocationEquiv h S)) P) *
    (∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (allocationEquiv h S)) P) = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.mul_sum, Finset.sum_eq_single S]
  · exact hilbertBlock_idempotent _ hPP
  · intro T _ hTS
    exact hilbertBlock_orthogonal _ _ (pairWordEmbedding_orthogonal h hTS.symm) P P
  · simp

theorem pairTypeProjection_tensor_commute {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) {C : Type*} [Fintype C]
    (A B : Matrix C C ℂ) :
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin *
        pairTypeProjection h α β C =
      pairTypeProjection h α β C *
        (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin := by
  unfold pairTypeProjection
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  apply hilbertBlock_intertwine _ _
    (TensorProduct.map (wordTensorMatrix u A).toEuclideanLin (wordTensorMatrix v B).toEuclideanLin)
  · exact pairWordEmbedding_tensor h S A B
  · simp only [TensorProduct.adjoint_map, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← wordTensorMatrix_star, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
    exact pairWordEmbedding_tensor h S A.conjTranspose B.conjTranspose
  · rw [← TensorProduct.map_mul, ← TensorProduct.map_mul,
      wordTypeProjection_tensor_commute, wordTypeProjection_tensor_commute]

end SignedSweeps
end

end OAI
