import OAI.Analysis.Triangular.Construction.L1Kernel
import OAI.Analysis.Triangular.Auxiliary.MatrixNorm

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.L1Kernel
lemma operator_apply {α β : Type*} (K : β → α → ℝ)
    (hK : ∀ j, Summable (fun i => |K i j|)) (C : ℝ)
    (hB : ∀ j, ∑' i, |K i j| ≤ C) (a : ℓ¹(α,ℝ)) (i : β) :
    operator K hK C hB a i = ∑' j, a j * K i j := by
  have hh := (lp.evalCLM ℝ (fun _ : β => ℝ) 1 i).map_tsum (summable_columns K hK C hB a)
  change (∑' j, a j • column K hK j) i = ∑' j, a j*K i j at ⊢
  change (∑' j, a j • column K hK j) i = ∑' j, (a j • column K hK j) i at hh
  simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,column] using hh
end AtomicTriangular.L1Kernel
namespace AtomicTriangular.MatrixBounds
open L1Kernel
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]
def l1Matrix (A : Matrix m n ℝ) : ℓ¹(n,ℝ) →L[ℝ] ℓ¹(m,ℝ) :=
  operator A (fun j => (hasSum_fintype _).summable) (matNorm A)
    (fun j => by simpa [tsum_fintype,colNorm] using colNorm_le_matNorm A j)
omit [Nonempty m] in
lemma l1Matrix_apply (A : Matrix m n ℝ) (x : ℓ¹(n,ℝ)) (i : m) :
    l1Matrix A x i = ∑ j, A i j*x j := by
  have hh := operator_apply A (fun j => (hasSum_fintype _).summable) (matNorm A)
    (fun j => by simpa [tsum_fintype,colNorm] using colNorm_le_matNorm A j) x i
  simpa only [l1Matrix,tsum_fintype,mul_comm] using hh
omit [Nonempty m] in
lemma l1Matrix_norm (A : Matrix m n ℝ) : ‖l1Matrix A‖ ≤ matNorm A :=
  operator_norm _ _ _ (matNorm_nonneg A) _
omit [Nonempty m] in
lemma l1Matrix_mul (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    l1Matrix (A*B) = (l1Matrix A).comp (l1Matrix B) := by
  ext x i
  simp only [l1Matrix_apply,ContinuousLinearMap.comp_apply,Matrix.mul_apply,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma l1Matrix_one [DecidableEq n] : l1Matrix (1:Matrix n n ℝ) = 1 := by
  ext x i
  simp [l1Matrix_apply,Matrix.one_apply]
omit [Nonempty m] in
lemma l1Matrix_add (A B : Matrix m n ℝ) : l1Matrix (A+B)=l1Matrix A+l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,add_mul,Finset.sum_add_distrib]
omit [Nonempty m] in
lemma l1Matrix_sub (A B : Matrix m n ℝ) : l1Matrix (A-B)=l1Matrix A-l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,sub_mul,Finset.sum_sub_distrib]
lemma l1Matrix_inverse [DecidableEq n] (A : Matrix n n ℝ) (hA : IsUnit A) :
    (l1Matrix A).comp (l1Matrix A⁻¹)=1 ∧ (l1Matrix A⁻¹).comp (l1Matrix A)=1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor
  · rw [←l1Matrix_mul,Matrix.mul_nonsing_inv A hd,l1Matrix_one]
  · rw [←l1Matrix_mul,Matrix.nonsing_inv_mul A hd,l1Matrix_one]
end AtomicTriangular.MatrixBounds
end

end OAI
