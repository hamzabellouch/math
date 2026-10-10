import OAI.Probability.SignedSweeps.HilbertBlockLower

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _

lemma pairWordEmbedding_twirl {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) (S : EvenAllocation u p)
    {A B : Matrix C C ℂ} {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p A B)
    (D : Matrix (Fin u → C) (Fin u → C) ℂ)
    (E : Matrix (Fin v → C) (Fin v → C) ℂ)
    (hDE : pairMatrixCompression (allocationEquiv h S) (matrixHilbertEquiv M) =
      Matrix.kroneckerMap (· * ·) D E) :
    M.toEuclideanLin ∘ₗ (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap =
      (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap ∘ₗ
        TensorProduct.map D.toEuclideanLin E.toEuclideanLin := by
  have ht := euclideanMatrix_intertwine (pairColorEmbedding (allocationEquiv h S))
    (Matrix.kroneckerMap (· * ·) D E) M (by
      intro w z
      exact congrFun (congrFun hDE w) z) (by
      intro w hw z
      apply pair_twirl_parity_off hM
      change wordEvenSites w ≠ wordEvenSites (pairColorWord (allocationEquiv h S) z)
      rw [pairColorWord_evenSites]
      exact fun he => hw ((pairColorEmbedding_range h S w).mpr he))
  change M.toEuclideanLin ∘ₗ
      ((euclideanEmbedding (pairColorEmbedding (allocationEquiv h S))).toLinearMap ∘ₗ
        (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap) = _
  let L := (euclideanEmbedding (pairColorEmbedding (C := C) (allocationEquiv h S))).toLinearMap
  let T := (euclideanTensorEquiv (I := Fin u → C) (J := Fin v → C)).toLinearEquiv.toLinearMap
  exact (congrArg (fun K => K ∘ₗ T) ht).trans
    (congrArg (fun K => L ∘ₗ K) (euclideanTensorEquiv_matrix_map D E)).symm

lemma pair_diagonal_tensor_positive {p : ℕ} {C : Type*} [Fintype C]
    (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (wordTensorMatrix p (Matrix.fromBlocks (Matrix.diagonal (fun i => (x i : ℂ))) 0 0
      (Matrix.diagonal (fun i => (y i : ℂ))))).PosSemidef := by
  have he : Matrix.fromBlocks (Matrix.diagonal (fun i => (x i : ℂ))) 0 0
      (Matrix.diagonal (fun i => (y i : ℂ))) =
      Matrix.diagonal (fun c : C ⊕ C => ((Sum.elim x y c : ℝ) : ℂ)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.diagonal_apply]
  rw [he]
  apply wordTensor_diagonal_positive
  intro i
  cases i with | inl i => exact hx i | inr i => exact hy i

theorem exists_pair_density_lower {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) (α : Partition u) (β : Partition v)
    (e : Fin (α.1.colLen 0) ↪ C) (f : Fin (β.1.colLen 0) ↪ C)
    (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ∃ M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ,
      matrixHilbertEquiv M ∈ pairTensorOrbitHull p
        (Matrix.diagonal (fun i => (x i : ℂ))) (Matrix.diagonal (fun i => (y i : ℂ))) ∧
      M.PosSemidef ∧
      ((wordMatrixEquiv p (C ⊕ C)).symm M -
        ((((∏ i, x (rowColorWord α e i)) / ((u + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))) *
          ((∏ i, y (rowColorWord β f i)) / ((v + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))) : ℝ) : ℂ) •
        pairTypeProjection h α β C).IsPositive := by
  obtain ⟨D,hD,hDpos,hDlow⟩ := exists_word_density_lower α e x hx
  obtain ⟨E,hE,hEpos,hElow⟩ := exists_word_density_lower β f y hy
  let e₀ : (Fin u ⊕ Fin v) ≃ Fin p := finSumFinEquiv.trans (finCongr h)
  obtain ⟨M,hM,hcomp⟩ := exists_pair_twirl_lift e₀ _ _ D E hD hE
  have hMpos : M.PosSemidef := matrix_twirl_positive (pairWordUnitaryHom p) hM
    (pair_diagonal_tensor_positive x y hx hy)
  refine ⟨M,hM,hMpos,?_⟩
  let L := TensorProduct.map ((wordMatrixEquiv u C).symm D) ((wordMatrixEquiv v C).symm E)
  have hLpos : L.IsPositive := tensor_map_positive _ _
    (Matrix.isPositive_toEuclideanLin_iff.mpr hDpos)
    (Matrix.isPositive_toEuclideanLin_iff.mpr hEpos)
  let a : ℝ := (∏ i, x (rowColorWord α e i)) / ((u + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))
  let b : ℝ := (∏ i, y (rowColorWord β f i)) / ((v + 1 : ℝ) ^ (Fintype.card C * Fintype.card C))
  have ha : 0 ≤ a := div_nonneg (Finset.prod_nonneg (fun i _ => hx _)) (by positivity)
  have hlow : (L - ((a * b : ℝ) : ℂ) •
      TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)).IsPositive :=
    tensor_map_lower _ _ _ _ (wordTypeProjection_positive α C)
      (Matrix.isPositive_toEuclideanLin_iff.mpr hEpos) a b ha hDlow hElow
  apply hilbertBlock_sum_lower (fun S => pairWordEmbedding (C := C) (allocationEquiv h S))
    (fun _ _ hST => pairWordEmbedding_orthogonal h hST) _
    (Matrix.isPositive_toEuclideanLin_iff.mpr hMpos)
    (fun _ => L) _ (fun _ => hLpos.isSymmetric) _ _ (fun _ => hlow)
  intro S
  simp only [L, wordMatrixEquiv_symm]
  apply pairWordEmbedding_twirl h S hM D E
  exact (pair_twirl_compression_eq hM _ e₀).trans hcomp

end SignedSweeps
end

end OAI
