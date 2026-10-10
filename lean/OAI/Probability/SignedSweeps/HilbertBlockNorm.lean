import OAI.Probability.SignedSweeps.PairWordTypes

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I E F : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma orthogonal_adjoint_norm_sq_le (j : I → E →ₗᵢ[ℂ] F)
    (hj : OrthogonalFamily ℂ (fun _ : I => E) j) (x : F) :
    ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let y := ∑ i, j i ((j i).toLinearMap.adjoint x)
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 := hj.norm_sum _ _
  have hi : (inner ℂ y x).re = ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 := by
    dsimp only [y]
    rw [sum_inner]
    change Complex.reCLM (∑ i, inner ℂ (j i ((j i).toLinearMap.adjoint x)) x) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ ((j i).toLinearMap ((j i).toLinearMap.adjoint x)) x).re = _
    rw [← LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  have hb := (Complex.re_le_norm (inner ℂ y x)).trans (norm_inner_le_norm y x)
  rw [hi, ← hn] at hb
  have hnorm : ‖y‖ ≤ ‖x‖ := by nlinarith [norm_nonneg y, norm_nonneg x]
  rw [← hn]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm _

lemma hilbertBlock_sum_norm_le (j : I → E →ₗᵢ[ℂ] F)
    (hj : OrthogonalFamily ℂ (fun _ : I => E) j) (A : I → E →ₗ[ℂ] E)
    {b : ℝ} (hb : 0 ≤ b) (hA : ∀ i x, ‖A i x‖ ≤ b * ‖x‖) (x : F) :
    ‖(∑ i, hilbertBlock (j i) (A i)) x‖ ≤ b * ‖x‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg hb (norm_nonneg _))
  simp only [LinearMap.sum_apply, hilbertBlock_apply]
  rw [hj.norm_sum]
  calc
    _ ≤ ∑ i, (b * ‖(j i).toLinearMap.adjoint x‖) ^ 2 :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hA i _) _)
    _ = b ^ 2 * ∑ i, ‖(j i).toLinearMap.adjoint x‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ b ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left
      (orthogonal_adjoint_norm_sq_le j hj x) (sq_nonneg _)
    _ = _ := (mul_pow _ _ _).symm

lemma hilbertBlock_left_intertwine (j : E →ₗᵢ[ℂ] F) (L : F →ₗ[ℂ] F)
    (A P : E →ₗ[ℂ] E) (hL : L ∘ₗ j.toLinearMap = j.toLinearMap ∘ₗ A) :
    L * hilbertBlock j P = hilbertBlock j (A * P) := by
  ext x
  exact LinearMap.congr_fun hL (P (j.toLinearMap.adjoint x))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma pairTypeProjection_norm_le {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C]
    (x : WordSpace p (C ⊕ C)) : ‖pairTypeProjection h α β C x‖ ≤ ‖x‖ :=
  symmetric_projection_contraction _ (pairTypeProjection_positive h α β C).isSymmetric
    (pairTypeProjection_idempotent h α β C) x

theorem pairTypeProjection_norm_of_factors {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) {C : Type*} [Fintype C]
    (A B : Matrix C C ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ x, ‖(((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C) x‖ ≤ a * ‖x‖)
    (hB : ∀ x, ‖(((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C) x‖ ≤ b * ‖x‖)
    (x : WordSpace p (C ⊕ C)) :
    ‖(((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β C) x‖ ≤ (a * b) * ‖x‖ := by
  let L := TensorProduct.map
    (((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C)
    (((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C)
  have he : ((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β C = ∑ S : EvenAllocation u p,
        hilbertBlock (pairWordEmbedding (allocationEquiv h S)) L := by
    unfold pairTypeProjection
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    simp only [L, wordMatrixEquiv_symm]
    erw [hilbertBlock_left_intertwine _ _ _ _ (pairWordEmbedding_tensor h S A B)]
    rw [← TensorProduct.map_mul]
  have hL : ∀ y, ‖L y‖ ≤ (a * b) * ‖y‖ := by
    have hN := tensor_map_norm_le
      (((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C)
      (((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C)
    have hAN : ‖(((wordMatrixEquiv u C).symm (wordTensorMatrix u A)) * wordTypeProjection α C).toContinuousLinearMap‖ ≤ a :=
      ContinuousLinearMap.opNorm_le_bound _ ha hA
    have hBN : ‖(((wordMatrixEquiv v C).symm (wordTensorMatrix v B)) * wordTypeProjection β C).toContinuousLinearMap‖ ≤ b :=
      ContinuousLinearMap.opNorm_le_bound _ hb hB
    have hLN : ‖L.toContinuousLinearMap‖ ≤ a * b :=
      hN.trans (mul_le_mul hAN hBN (norm_nonneg _) ha)
    intro y
    exact (L.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hLN (norm_nonneg _))
  rw [he]
  exact hilbertBlock_sum_norm_le _ (fun _ _ hST => pairWordEmbedding_orthogonal h hST)
    _ (mul_nonneg ha hb) (fun _ => hL) x

end SignedSweeps
end

end OAI
