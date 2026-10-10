import OAI.Probability.SignedSweeps.WordAllocations

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
lemma euclideanMatrix_single (A : Matrix J I ℂ) (i : I) (j : J) :
    A.toEuclideanLin (EuclideanSpace.single i 1) j = A j i := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma euclideanMatrix_intertwine (e : I ↪ J) (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (hB : ∀ i k, B (e i) (e k) = A i k)
    (hzero : ∀ j, j ∉ Set.range e → ∀ k, B j (e k) = 0) :
    B.toEuclideanLin ∘ₗ (euclideanEmbedding e).toLinearMap =
      (euclideanEmbedding e).toLinearMap ∘ₗ A.toEuclideanLin := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  change B.toEuclideanLin (euclideanEmbedding e (EuclideanSpace.single i 1)) =
    euclideanEmbedding e (A.toEuclideanLin (EuclideanSpace.single i 1))
  rw [euclideanEmbedding_single]
  ext j
  rw [euclideanMatrix_single]
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k,rfl⟩ := hj
    rw [euclideanEmbedding_apply, euclideanEmbeddingLinear_at, euclideanMatrix_single, hB]
  · rw [hzero j hj, euclideanEmbedding_apply, euclideanEmbeddingLinear_off e _ hj]

lemma euclideanTensorEquiv_matrix_map (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (euclideanTensorEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap ∘ₗ
        TensorProduct.map A.toEuclideanLin B.toEuclideanLin =
      (Matrix.kroneckerMap (· * ·) A B).toEuclideanLin ∘ₗ
        (euclideanTensorEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap := by
  apply ((EuclideanSpace.basisFun I ℂ).tensorProduct
    (EuclideanSpace.basisFun J ℂ)).toBasis.ext
  rintro ⟨i,j⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change euclideanTensorEquiv (TensorProduct.map A.toEuclideanLin B.toEuclideanLin
    (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1)) =
      (Matrix.kroneckerMap (· * ·) A B).toEuclideanLin
        (euclideanTensorEquiv (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1))
  rw [TensorProduct.map_tmul, euclideanTensorEquiv_single]
  ext ⟨k,l⟩
  rw [euclideanTensorEquiv_tmul, euclideanMatrix_single, euclideanMatrix_single]
  simp only [Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.kroneckerMap_apply]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTensorMatrix_pairColor {u v p : ℕ} {C : Type*}
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (A B : Matrix C C ℂ)
    (w z : (Fin u → C) × (Fin v → C)) :
    wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)
      (pairColorWord e w) (pairColorWord e z) =
      wordTensorMatrix u A w.1 z.1 * wordTensorMatrix v B w.2 z.2 := by
  unfold wordTensorMatrix
  rw [← e.prod_comp, Fintype.prod_sum_type]
  simp only [pairColorWord, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

lemma wordTensorMatrix_parity_off {p : ℕ} {C : Type*} (A B : Matrix C C ℂ)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w ≠ wordEvenSites z) :
    wordTensorMatrix p (Matrix.fromBlocks A 0 0 B) w z = 0 := by
  by_contra hn
  apply h
  ext i
  have hi := Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ _)
  cases hw : w i <;> cases hz : z i <;>
    simp [mem_wordEvenSites, hw, hz] at hi ⊢

theorem pairWordEmbedding_tensor {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) (S : EvenAllocation u p) (A B : Matrix C C ℂ) :
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin ∘ₗ
      (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
    (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap ∘ₗ
      TensorProduct.map (wordTensorMatrix u A).toEuclideanLin
        (wordTensorMatrix v B).toEuclideanLin := by
  have ht := euclideanMatrix_intertwine (pairColorEmbedding (allocationEquiv h S))
    (Matrix.kroneckerMap (· * ·) (wordTensorMatrix u A) (wordTensorMatrix v B))
    (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)) (by
      intro w z
      exact wordTensorMatrix_pairColor _ A B w z) (by
      intro w hw z
      apply wordTensorMatrix_parity_off
      change wordEvenSites w ≠ wordEvenSites (pairColorWord (allocationEquiv h S) z)
      rw [pairColorWord_evenSites]
      exact fun he => hw ((pairColorEmbedding_range h S w).mpr he))
  change (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin ∘ₗ
      ((euclideanEmbedding (pairColorEmbedding (allocationEquiv h S))).toLinearMap ∘ₗ
        (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap) = _
  let L := (euclideanEmbedding (pairColorEmbedding (C := C) (allocationEquiv h S))).toLinearMap
  let T := (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap
  have hh := congrArg (fun M => M ∘ₗ T) ht
  have hh' := congrArg (fun M => L ∘ₗ M)
    (euclideanTensorEquiv_matrix_map (wordTensorMatrix u A) (wordTensorMatrix v B))
  exact hh.trans hh'.symm

end SignedSweeps
end

end OAI
