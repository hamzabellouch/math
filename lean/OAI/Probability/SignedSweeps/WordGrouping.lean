import OAI.Probability.SignedSweeps.PiTensorMatrix

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) wordGroupingDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

def groupWordEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) :
    (Fin p → C) ≃ (∀ j, Fin (k j) → C) where
  toFun w j i := w (e ⟨j,i⟩)
  invFun w i := w (e.symm i).1 (e.symm i).2
  left_inv w := by
    funext i
    change w (e (e.symm i)) = w i
    rw [Equiv.apply_symm_apply]
  right_inv w := by
    funext j i
    change (fun x : Σ j, Fin (k j) => w x.1 x.2) (e.symm (e ⟨j,i⟩)) = w j i
    rw [Equiv.symm_apply_apply]

def groupedWordMatrix (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ :=
  (piTensorMatrix A).submatrix (groupWordEquiv e) (groupWordEquiv e)

lemma groupedWordMatrix_mul (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    groupedWordMatrix e (fun j => A j * B j) =
      groupedWordMatrix e A * groupedWordMatrix e B := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_mul, Matrix.submatrix_mul_equiv]

omit [Fintype C] in
lemma groupedWordMatrix_one (e : (Σ j, Fin (k j)) ≃ Fin p) :
    groupedWordMatrix (C := C) e (fun j => (1 : Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)) = 1 := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_one, Matrix.submatrix_one_equiv]

omit [Fintype C] in
lemma groupedWordMatrix_star (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    groupedWordMatrix e (fun j => (A j).conjTranspose) = (groupedWordMatrix e A).conjTranspose := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_star, Matrix.conjTranspose_submatrix]

lemma groupedWordMatrix_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, (A j).PosSemidef) : (groupedWordMatrix e A).PosSemidef :=
  (piTensorMatrix_positive A hA).submatrix _

lemma groupedWordMatrix_lower (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hAB : ∀ j, (A j - B j).PosSemidef) :
    (groupedWordMatrix e A - groupedWordMatrix e B).PosSemidef :=
  (piTensorMatrix_lower A B hA hB hAB).submatrix _

omit [Fintype C] in
lemma groupedWordMatrix_scale (e : (Σ j, Fin (k j)) ≃ Fin p)
    (a : J → ℂ) (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    groupedWordMatrix e (fun j => a j • A j) = (∏ j, a j) • groupedWordMatrix e A := by
  unfold groupedWordMatrix
  rw [piTensorMatrix_scale, Matrix.submatrix_smul]
  rfl

lemma groupedWordMatrix_trace (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    (groupedWordMatrix e A).trace = ∏ j, (A j).trace := by
  unfold groupedWordMatrix
  rw [← piTensorMatrix_trace]
  exact (groupWordEquiv (C := C) e).sum_comp (fun w => piTensorMatrix A w w)

omit [Fintype C] in
lemma groupedWordMatrix_tensor (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : J → Matrix C C ℂ) :
    groupedWordMatrix e (fun j => wordTensorMatrix (k j) (A j)) =
      varyingWordTensor (fun i => A (e.symm i).1) := by
  ext w z
  change (∏ j, ∏ i, A j (w (e ⟨j,i⟩)) (z (e ⟨j,i⟩))) =
    ∏ i, A (e.symm i).1 (w i) (z i)
  calc
    _ = ∏ x : Σ j, Fin (k j), A x.1 (w (e x)) (z (e x)) :=
      (Fintype.prod_sigma (fun x : Σ j, Fin (k j) => A x.1 (w (e x)) (z (e x)))).symm
    _ = _ := by
      simpa only [Equiv.symm_apply_apply] using
        e.prod_comp (fun i => A (e.symm i).1 (w i) (z i))

omit [Fintype C] in
lemma groupedWordMatrix_const_tensor (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : Matrix C C ℂ) :
    groupedWordMatrix e (fun j => wordTensorMatrix (k j) A) = wordTensorMatrix p A := by
  rw [groupedWordMatrix_tensor]
  rfl

lemma groupedWordMatrix_commute (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (h : ∀ j, A j * B j = B j * A j) :
    groupedWordMatrix e A * groupedWordMatrix e B = groupedWordMatrix e B * groupedWordMatrix e A := by
  rw [← groupedWordMatrix_mul, ← groupedWordMatrix_mul]
  simp only [h]

def groupedWordOperator (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C) :
    WordSpace p C →ₗ[ℂ] WordSpace p C :=
  (wordMatrixEquiv p C).symm (groupedWordMatrix e (fun j => wordMatrixEquiv (k j) C (A j)))

lemma groupedWordOperator_mul (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A B : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C) :
    groupedWordOperator e (fun j => A j * B j) = groupedWordOperator e A * groupedWordOperator e B := by
  simp only [groupedWordOperator, map_mul, groupedWordMatrix_mul]

lemma groupedWordOperator_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C)
    (hA : ∀ j, (A j).IsPositive) : (groupedWordOperator e A).IsPositive := by
  apply Matrix.isPositive_toEuclideanLin_iff.mpr
  apply groupedWordMatrix_positive
  intro j
  exact Matrix.isPositive_toEuclideanLin_iff.mp (by simpa using hA j)

lemma groupedWordOperator_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C)
    (hA : ∀ j, A j * A j = A j) : groupedWordOperator e A * groupedWordOperator e A = groupedWordOperator e A := by
  rw [← groupedWordOperator_mul]
  simp only [hA]

lemma groupedWordMatrix_toEuclideanLin (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    (groupedWordMatrix e A).toEuclideanLin = groupedWordOperator e (fun j => (A j).toEuclideanLin) := by
  change (wordMatrixEquiv p C).symm (groupedWordMatrix e A) =
    (wordMatrixEquiv p C).symm (groupedWordMatrix e (fun j => wordMatrixEquiv (k j) C (A j).toEuclideanLin))
  congr 2
  funext j
  exact ((wordMatrixEquiv (k j) C).apply_symm_apply (A j)).symm

end SignedSweeps
end

end OAI
