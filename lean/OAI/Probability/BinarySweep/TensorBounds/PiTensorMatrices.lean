import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
  [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]

def piTensorMatrices (M : ∀ i, Matrix (A i) (B i) ℂ) :
    Matrix (∀ i, A i) (∀ i, B i) ℂ := fun x y => ∏ i, M i (x i) (y i)

omit [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, DecidableEq (B index)] [∀ index, Fintype (C index)]
  [∀ index, DecidableEq (C index)] in
lemma piTensorMatrices_mul (M : ∀ i, Matrix (A i) (B i) ℂ)
    (N : ∀ i, Matrix (B i) (C i) ℂ) :
    piTensorMatrices M * piTensorMatrices N = piTensorMatrices (fun i => M i*N i) := by
  ext x z
  simp only [Matrix.mul_apply,piTensorMatrices,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => M i (x i) b * N i b (z i))).symm

omit [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)] in
lemma piTensorMatrices_star (M : ∀ i, Matrix (A i) (B i) ℂ) :
    (piTensorMatrices M).conjTranspose = piTensorMatrices (fun i => (M i).conjTranspose) := by
  ext x y
  simp [piTensorMatrices]

omit [DecidableEq I] [∀ index, Fintype (A index)] in
lemma piTensorMatrices_one : piTensorMatrices (fun i : I => (1 : Matrix (A i) (A i) ℂ))=1 := by
  ext x y
  by_cases h : x=y
  · subst y; simp [piTensorMatrices]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [piTensorMatrices,Matrix.one_apply,ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma piTensorMatrices_psd (M : ∀ i, Matrix (A i) (A i) ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (piTensorMatrices M).PosSemidef := by
  have hx (i : I) : ∃ X : Matrix (A i) (A i) ℂ, M i=X.conjTranspose*X :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM i).nonneg
  choose X hX using hx
  have he : piTensorMatrices M = (piTensorMatrices X).conjTranspose*piTensorMatrices X := by
    rw [piTensorMatrices_star,piTensorMatrices_mul]
    congr 1
    funext i
    exact hX i
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [∀ index, DecidableEq (A index)] in
lemma piTensorMatrices_trace (M : ∀ i, Matrix (A i) (A i) ℂ) :
    (piTensorMatrices M).trace = ∏ i, (M i).trace := by
  simp only [Matrix.trace,Matrix.diag,piTensorMatrices]
  exact (Fintype.prod_sum (fun i a => M i a a)).symm

omit [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)] in
lemma piTensorMatrices_smul (c : I → ℂ) (M : ∀ i, Matrix (A i) (B i) ℂ) :
    piTensorMatrices (fun i => c i • M i) = (∏i, c i) • piTensorMatrices M := by
  ext x y
  simp only [piTensorMatrices,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

omit [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)]
  [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)] in
lemma piTensorMatrices_sum {W : I → Type*} [∀ i, Fintype (W i)]
    (M : ∀ i, W i → Matrix (A i) (B i) ℂ) :
    piTensorMatrices (fun i => ∑w, M i w) = ∑f : ∀ i, W i, piTensorMatrices (fun i => M i (f i)) := by
  ext x y
  simp only [piTensorMatrices,Matrix.sum_apply]
  exact Fintype.prod_sum (fun i w => M i w (x i) (y i))

lemma piTensorMatrices_mono (M N : ∀ i, Matrix (A i) (A i) ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hMN : ∀ i, (N i-M i).PosSemidef) :
    (piTensorMatrices N-piTensorMatrices M).PosSemidef := by
  let T (i : I) (b : Bool) := if b then N i-M i else M i
  have he : piTensorMatrices N = ∑f : I → Bool, piTensorMatrices (fun i => T i (f i)) := by
    rw [← piTensorMatrices_sum]
    congr 1
    funext i
    simp [T]
  have hf : piTensorMatrices M = piTensorMatrices (fun i => T i false) := by simp [T]
  rw [he,hf,← Finset.sum_erase_add _ _ (Finset.mem_univ (fun _ : I => false)),add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro f _
  apply piTensorMatrices_psd
  intro i
  dsimp [T]
  split
  · exact hMN i
  · exact hM i

theorem piTensor_density_domination {W : I → Type*} [∀ i, Fintype (W i)]
    (P : ∀ i, Matrix (A i) (A i) ℂ) (r : ∀ i, W i → Matrix (A i) (A i) ℂ)
    (c : I → ℂ) (hP : ∀ i, (P i).PosSemidef)
    (hdom : ∀ i, (c i • ∑w, r i w-P i).PosSemidef) :
    ((∏i, c i) • (∑f : ∀ i, W i, piTensorMatrices (fun i => r i (f i)))-piTensorMatrices P).PosSemidef := by
  have h := piTensorMatrices_mono P (fun i => c i • ∑w, r i w) hP hdom
  rwa [piTensorMatrices_smul,piTensorMatrices_sum] at h

end BinaryCoordinateSweeps.Density

end

end OAI
