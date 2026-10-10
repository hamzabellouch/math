import OAI.Probability.SignedSweeps.PairCentral
import OAI.Probability.SignedSweeps.GroupedDensity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
local instance (priority := 2000) parityCutWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) parityCutSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma colorParity_cut_blocks {C : Type*} (A : Matrix (C ⊕ C) (C ⊕ C) ℂ) :
    colorClassCut colorParity A = Matrix.fromBlocks
      (A.submatrix Sum.inl Sum.inl) 0 0 (A.submatrix Sum.inr Sum.inr) := by
  ext i j
  cases i <;> cases j <;> simp [colorClassCut_apply, colorParity]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
local instance (priority := 2000) groupedCommuteWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) groupedCommuteSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

lemma groupedPairTypeProjection_tensor_commute
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    (A B : Matrix C C ℂ) :
    groupedPairTypeProjection e h α β * (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin =
      (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)).toEuclideanLin * groupedPairTypeProjection e h α β := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C)
      (groupedPairTypeProjection e h α β * (wordMatrixEquiv p (C ⊕ C)).symm
        (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) =
    wordMatrixEquiv p (C ⊕ C)
      ((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B)) *
        groupedPairTypeProjection e h α β)
  simp only [map_mul, groupedPairTypeProjection, groupedWordOperator, StarAlgEquiv.apply_symm_apply]
  rw [← groupedWordMatrix_const_tensor e (Matrix.fromBlocks A 0 0 B)]
  apply groupedWordMatrix_commute
  intro j
  have hh := congrArg (wordMatrixEquiv (k j) (C ⊕ C))
    (pairTypeProjection_tensor_commute (h j) (α j) (β j) A B)
  change wordMatrixEquiv (k j) (C ⊕ C)
      ((wordMatrixEquiv (k j) (C ⊕ C)).symm (wordTensorMatrix (k j) (Matrix.fromBlocks A 0 0 B)) *
      pairTypeProjection (h j) (α j) (β j) C) =
    wordMatrixEquiv (k j) (C ⊕ C)
      (pairTypeProjection (h j) (α j) (β j) C *
        (wordMatrixEquiv (k j) (C ⊕ C)).symm (wordTensorMatrix (k j) (Matrix.fromBlocks A 0 0 B))) at hh
  simpa only [map_mul, StarAlgEquiv.apply_symm_apply] using hh.symm

lemma groupedPairTypeProjection_even_commute
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    (R : EvenColorDensity C) :
    R.tensor p * groupedPairTypeProjection e h α β = groupedPairTypeProjection e h α β * R.tensor p :=
  (groupedPairTypeProjection_tensor_commute e h α β R.even R.odd).symm

lemma groupedPairTypeProjection_global_commute
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    {u₀ v₀ : ℕ} (h₀ : u₀+v₀=p) (α₀ : Partition u₀) (β₀ : Partition v₀) :
    groupedPairTypeProjection (C := C) e h α β * pairTypeProjection h₀ α₀ β₀ C =
      pairTypeProjection h₀ α₀ β₀ C * groupedPairTypeProjection e h α β := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  simp only [map_mul]
  have hs := pairTypeProjection_even_span (C := C) h₀ α₀ β₀
  generalize hx : wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h₀ α₀ β₀ C) = X at hs ⊢
  clear hx
  induction hs using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨A,rfl⟩ := hA
    dsimp only
    rw [colorParity_cut_blocks]
    have hh := congrArg (wordMatrixEquiv p (C ⊕ C))
      (groupedPairTypeProjection_tensor_commute e h α β
        (A.submatrix Sum.inl Sum.inl) (A.submatrix Sum.inr Sum.inr))
    change wordMatrixEquiv p (C ⊕ C)
        (groupedPairTypeProjection e h α β * (wordMatrixEquiv p (C ⊕ C)).symm
          (wordTensorMatrix p (Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0
            (A.submatrix Sum.inr Sum.inr)))) =
      wordMatrixEquiv p (C ⊕ C)
        ((wordMatrixEquiv p (C ⊕ C)).symm
          (wordTensorMatrix p (Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0
            (A.submatrix Sum.inr Sum.inr))) * groupedPairTypeProjection e h α β) at hh
    simp only [map_mul, StarAlgEquiv.apply_symm_apply] at hh
    convert hh using 1
  | zero => simp
  | add A B _ _ hA hB => simp only [Matrix.mul_add, Matrix.add_mul, hA, hB]
  | smul c A _ hA => simp only [Matrix.mul_smul, Matrix.smul_mul, hA]

end SignedSweeps
end

end OAI
