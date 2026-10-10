import OAI.Combinatorics.ThinTrees.Subisotropic

namespace OAI

universe uD uO uI uI2

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {D : Type uD} {O : Type uO} [Fintype D] [DecidableEq D] [Fintype O] [DecidableEq O]

lemma blockDiagonal_nonneg (A : O → Matrix D D ℝ) (hA : ∀o, 0 ≤ A o) :
    0 ≤ Matrix.blockDiagonal A := by
  let S : O → Matrix D D ℝ := fun o => CFC.sqrt (A o)
  have hf : ∀o, (S o)ᴴ*S o=A o := by
    intro o
    rw [(CFC.sqrt_nonneg (A o)).posSemidef.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self (A o) (hA o)
  have he : (Matrix.blockDiagonal S)ᴴ*Matrix.blockDiagonal S=Matrix.blockDiagonal A := by
    rw [Matrix.blockDiagonal_conjTranspose,←Matrix.blockDiagonal_mul]
    simp only [hf]
  rw [←he]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg

lemma blockDiagonal_mono (A B : O → Matrix D D ℝ) (h : ∀o, A o ≤ B o) :
    Matrix.blockDiagonal A ≤ Matrix.blockDiagonal B := by
  apply sub_nonneg.mp
  rw [←Matrix.blockDiagonal_sub]
  exact blockDiagonal_nonneg _ (fun o => sub_nonneg.mpr (h o))

omit [Fintype D] [DecidableEq D] [Fintype O] [DecidableEq O] in
lemma blockDiag_mono {A B : Matrix (D × O) (D × O) ℝ} (h : A ≤ B) (o : O) :
    Matrix.blockDiag A o ≤ Matrix.blockDiag B o := by
  have hh := (sub_nonneg.mpr h).posSemidef.submatrix (fun d : D => (d,o))
  change (Matrix.blockDiag (B-A) o).PosSemidef at hh
  simpa only [Matrix.blockDiag_sub,Pi.sub_apply,sub_nonneg] using hh.nonneg

omit [Fintype O] [DecidableEq O] [Fintype D] [DecidableEq D] in
lemma blockDiag_sum {I : Type uI} (s : Finset I) (A : I → Matrix (D × O) (D × O) ℝ) (o : O) :
    Matrix.blockDiag (∑i ∈ s, A i) o=∑i ∈ s, Matrix.blockDiag (A i) o := by
  ext a b
  simp [Matrix.blockDiag_apply,Matrix.sum_apply]

omit [Fintype D] [DecidableEq D] in
def blockEmbed (v : D → ℝ) (b : Bool) : D × Bool → ℝ :=
  fun p => if p.2=b then v p.1 else 0

omit [DecidableEq D] in
lemma blockEmbed_trace (v : D → ℝ) (b : Bool) :
    (Matrix.vecMulVec (blockEmbed v b) (blockEmbed v b)).trace=(Matrix.vecMulVec v v).trace := by
  cases b <;> simp [Matrix.trace,Matrix.diag,Matrix.vecMulVec,blockEmbed,Fintype.sum_prod_type]

omit [Fintype D] [DecidableEq D] in
lemma blockEmbed_mean (v : D → ℝ) :
    (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed v b) (blockEmbed v b))=
      Matrix.blockDiagonal (fun _ : Bool => (1/2 : ℝ) • Matrix.vecMulVec v v) := by
  ext ⟨a,c⟩ ⟨d,b⟩
  cases c <;> cases b <;>
    simp [Matrix.vecMulVec,blockEmbed,Matrix.blockDiagonal_apply]

omit [Fintype D] [DecidableEq D] in
lemma blockEmbed_blockDiag (v : D → ℝ) (b c : Bool) :
    Matrix.blockDiag (Matrix.vecMulVec (blockEmbed v b) (blockEmbed v b)) c=
      if b=c then Matrix.vecMulVec v v else 0 := by
  cases b <;> cases c <;> ext a d <;>
    simp [Matrix.blockDiag_apply,Matrix.vecMulVec,blockEmbed]

omit [Fintype O] [DecidableEq O] [Fintype D] [DecidableEq D] in
lemma blockDiagonal_sum {I : Type uI2} (s : Finset I) (A : I → O → Matrix D D ℝ) [DecidableEq O] :
    Matrix.blockDiagonal (fun o => ∑i ∈ s, A i o)=∑i ∈ s, Matrix.blockDiagonal (A i) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases h : b=d <;> simp [Matrix.blockDiagonal_apply,h,Matrix.sum_apply]

end StrongThinTree.MSS

end
end

end OAI
