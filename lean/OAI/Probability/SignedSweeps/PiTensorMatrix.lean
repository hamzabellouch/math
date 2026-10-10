import OAI.Probability.SignedSweeps.WordTensorBasis

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

def piTensorMatrix (A : ∀ j, Matrix (I j) (I j) ℂ) :
    Matrix (∀ j, I j) (∀ j, I j) ℂ := fun w z => ∏ j, A j (w j) (z j)

lemma piTensorMatrix_mul (A B : ∀ j, Matrix (I j) (I j) ℂ) :
    piTensorMatrix (fun j => A j * B j) = piTensorMatrix A * piTensorMatrix B := by
  ext x y
  simp only [piTensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

omit [∀ j, Fintype (I j)] in
lemma piTensorMatrix_one : piTensorMatrix (fun j => (1 : Matrix (I j) (I j) ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y; simp [piTensorMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [Matrix.one_apply, ite_eq_right h, piTensorMatrix]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

omit [∀ j, Fintype (I j)] in
lemma piTensorMatrix_star (A : ∀ j, Matrix (I j) (I j) ℂ) :
    piTensorMatrix (fun j => (A j).conjTranspose) = (piTensorMatrix A).conjTranspose := by
  ext x y
  simp only [piTensorMatrix, Matrix.conjTranspose_apply, star_prod]

lemma piTensorMatrix_idempotent (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, A j * A j = A j) : piTensorMatrix A * piTensorMatrix A = piTensorMatrix A := by
  rw [← piTensorMatrix_mul]
  simp only [hA]

lemma piTensorMatrix_commute (A B : ∀ j, Matrix (I j) (I j) ℂ)
    (h : ∀ j, A j * B j = B j * A j) :
    piTensorMatrix A * piTensorMatrix B = piTensorMatrix B * piTensorMatrix A := by
  rw [← piTensorMatrix_mul, ← piTensorMatrix_mul]
  simp only [h]

omit [∀ j, Fintype (I j)] in
lemma piTensorMatrix_scale (a : J → ℂ) (A : ∀ j, Matrix (I j) (I j) ℂ) :
    piTensorMatrix (fun j => a j • A j) = (∏ j, a j) • piTensorMatrix A := by
  ext x y
  simp only [piTensorMatrix, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

lemma piTensorMatrix_trace (A : ∀ j, Matrix (I j) (I j) ℂ) :
    (piTensorMatrix A).trace = ∏ j, (A j).trace := by
  simp only [Matrix.trace, Matrix.diag, piTensorMatrix]
  exact (Fintype.prod_sum (fun (j : J) (i : I j) => A j i i)).symm

omit [Fintype J] in
lemma kernel_product_positive {X : Type*} [Fintype X] (s : Finset J)
    (A : J → Matrix X X ℂ) (hA : ∀ j ∈ s, (A j).PosSemidef) :
    Matrix.PosSemidef (fun x y => ∏ j ∈ s, A j x y : Matrix X X ℂ) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : X => (1 : ℂ))
    have he : Matrix.vecMulVec (fun _ : X => (1 : ℂ)) (star (fun _ : X => (1 : ℂ))) =
        (fun _ _ => 1 : Matrix X X ℂ) := by ext x y; simp [Matrix.vecMulVec]
    rw [he] at h
    simpa only [Finset.prod_empty] using h
  | @insert j s hj ih =>
    have hh := (hA j (Finset.mem_insert_self _ _)).hadamard
      (ih (fun k hk => hA k (Finset.mem_insert_of_mem hk)))
    have he : (fun x y => ∏ k ∈ insert j s, A k x y : Matrix X X ℂ) =
        (A j).hadamard (fun x y => ∏ k ∈ s, A k x y) := by
      ext x y
      change (∏ k ∈ insert j s, A k x y) = A j x y * ∏ k ∈ s, A k x y
      rw [Finset.prod_insert hj]
    rw [he]
    exact hh

lemma piTensorMatrix_positive (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, (A j).PosSemidef) : (piTensorMatrix A).PosSemidef := by
  apply kernel_product_positive Finset.univ (fun j => (A j).submatrix (fun w : ∀ j, I j => w j) (fun w : ∀ j, I j => w j))
  intro j _
  exact (hA j).submatrix (fun w : ∀ j, I j => w j)

omit [Fintype J] in
lemma kernel_product_lower {X : Type*} [Fintype X] (s : Finset J)
    (A B : J → Matrix X X ℂ) (hA : ∀ j ∈ s, (A j).PosSemidef)
    (hB : ∀ j ∈ s, (B j).PosSemidef) (hAB : ∀ j ∈ s, (A j - B j).PosSemidef) :
    Matrix.PosSemidef ((fun x y => ∏ j ∈ s, A j x y) - (fun x y => ∏ j ∈ s, B j x y) : Matrix X X ℂ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self]
    exact Matrix.PosSemidef.zero
  | @insert j s hj ih =>
    let P : Matrix X X ℂ := fun x y => ∏ k ∈ s, A k x y
    let Q : Matrix X X ℂ := fun x y => ∏ k ∈ s, B k x y
    have hP : P.PosSemidef := kernel_product_positive s A (fun k hk => hA k (Finset.mem_insert_of_mem hk))
    have hPQ : (P - Q).PosSemidef := ih
      (fun k hk => hA k (Finset.mem_insert_of_mem hk))
      (fun k hk => hB k (Finset.mem_insert_of_mem hk))
      (fun k hk => hAB k (Finset.mem_insert_of_mem hk))
    have hh := ((hAB j (Finset.mem_insert_self _ _)).hadamard hP).add
      ((hB j (Finset.mem_insert_self _ _)).hadamard hPQ)
    have he : ((fun x y => ∏ k ∈ insert j s, A k x y) -
        (fun x y => ∏ k ∈ insert j s, B k x y) : Matrix X X ℂ) =
        (A j - B j).hadamard P + (B j).hadamard (P - Q) := by
      ext x y
      change (∏ k ∈ insert j s, A k x y) - (∏ k ∈ insert j s, B k x y) =
        (A j x y - B j x y) * (∏ k ∈ s, A k x y) +
          B j x y * ((∏ k ∈ s, A k x y) - (∏ k ∈ s, B k x y))
      simp only [Finset.prod_insert hj]
      ring
    rw [he]
    exact hh

lemma piTensorMatrix_lower (A B : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hAB : ∀ j, (A j - B j).PosSemidef) :
    (piTensorMatrix A - piTensorMatrix B).PosSemidef := by
  apply kernel_product_lower Finset.univ
    (fun j => (A j).submatrix (fun w : ∀ j, I j => w j) (fun w : ∀ j, I j => w j))
    (fun j => (B j).submatrix (fun w : ∀ j, I j => w j) (fun w : ∀ j, I j => w j))
  · intro j _; exact (hA j).submatrix (fun w : ∀ j, I j => w j)
  · intro j _; exact (hB j).submatrix (fun w : ∀ j, I j => w j)
  · intro j _; exact (hAB j).submatrix (fun w : ∀ j, I j => w j)

end SignedSweeps
end

end OAI
