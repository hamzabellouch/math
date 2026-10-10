import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [Fintype J]

def hsVector : Matrix I J ℂ →ₗ[ℂ] EuclideanSpace ℂ (I × J) where
  toFun M := WithLp.toLp 2 (fun z => M z.1 z.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma hsVector_inner (M N : Matrix I J ℂ) :
    inner ℂ (hsVector M) (hsVector N) = (M.conjTranspose*N).trace := by
  change (∑ z : I × J, N z.1 z.2 * star (M z.1 z.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma hsVector_norm_sq (M : Matrix I J ℂ) :
    ‖hsVector M‖^2 = (M.conjTranspose*M).trace.re := by
  rw [← hsVector_inner M M, inner_self_eq_norm_sq_to_K]
  simp only [← Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]

lemma trace_mH_mul_le (M N : Matrix I J ℂ) :
    (M.conjTranspose*N).trace.re ≤ Real.sqrt ((M.conjTranspose*M).trace.re) *
      Real.sqrt ((N.conjTranspose*N).trace.re) := by
  rw [← hsVector_inner M N, ← hsVector_norm_sq M, ← hsVector_norm_sq N,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

variable [DecidableEq I]

lemma trace_mul_psd_nonneg (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let R : Matrix I I ℂ := CFC.sqrt B
  have hs : R.conjTranspose=R := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hsq : R*R=B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hh := (hA.conjTranspose_mul_mul_same R).trace_nonneg
  rw [hs] at hh
  have ht : (R*A*R).trace=(A*B).trace := by
    rw [Matrix.trace_mul_cycle,hsq,Matrix.trace_mul_comm]
  rw [ht] at hh
  exact hh.1

lemma trace_mul_mono (A B T : Matrix I I ℂ) (h : A ≤ B) (hT : T.PosSemidef) :
    (A*T).trace.re ≤ (B*T).trace.re := by
  have hh := trace_mul_psd_nonneg (B-A) T h hT
  rw [sub_mul,Matrix.trace_sub,Complex.sub_re] at hh
  linarith

lemma trace_sqrt_conjugate_le_one (A B U : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hTA : A.trace.re ≤ 1) (hTB : B.trace.re ≤ 1) (hU : U ∈ unitary (Matrix I I ℂ)) :
    (CFC.sqrt A * U * CFC.sqrt B * U.conjTranspose).trace.re ≤ 1 := by
  let X : Matrix I I ℂ := CFC.sqrt A
  let Y : Matrix I I ℂ := U * CFC.sqrt B * U.conjTranspose
  have hx : X.conjTranspose=X := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hy : Y.conjTranspose=Y := by simp [Y,Matrix.conjTranspose_mul,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq, mul_assoc]
  have hy2 : Y*Y=U*B*U.conjTranspose := by
    have hu : U.conjTranspose*U=1 := hU.1
    dsimp only [Y]
    calc
      _=U*CFC.sqrt B*(U.conjTranspose*U)*CFC.sqrt B*U.conjTranspose := by noncomm_ring
      _=U*B*U.conjTranspose := by rw [hu,mul_one]; rw [mul_assoc U, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  have hx2 : X*X=A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have ht : (Y*Y).trace=B.trace := by
    rw [hy2,Matrix.trace_mul_cycle]
    have hu : U.conjTranspose*U=1 := hU.1
    rw [hu,one_mul]
  have hc := trace_mH_mul_le X Y
  rw [hx,hy,hx2,ht] at hc
  have hsA : Real.sqrt A.trace.re ≤ 1 := (Real.sqrt_le_one).mpr hTA
  have hsB : Real.sqrt B.trace.re ≤ 1 := (Real.sqrt_le_one).mpr hTB
  have hprod := mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hh := hc.trans hprod
  simpa only [X,Y,← mul_assoc,one_mul] using hh
end RowColumn.MatrixState

end
end

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

lemma toEuclideanCLM_positive_iff (A : Matrix I I ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact Matrix.isPositive_toEuclideanLin_iff

lemma trace_toEuclideanCLM (A : Matrix I I ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A).toLinearMap = A.trace := by
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun I ℂ).toBasis

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma hsVector_injective : Function.Injective (hsVector (I := I) (J := J)) := by
  intro a b h
  ext i j
  exact congrArg (fun v : EuclideanSpace ℂ (I × J) => v (i,j)) h

omit [DecidableEq I] [DecidableEq J] in
lemma hsVector_norm_sq_sum (M : Matrix I J ℂ) :
    ‖hsVector M‖^2 = ∑ i, ∑ j, ‖M i j‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

lemma finite_sum_embedding_le {D E : Type*} [Fintype D] [Fintype E]
    (e : D ↪ E) (f : E → ℝ) (hf : ∀ i, 0 ≤ f i) : ∑ i, f (e i) ≤ ∑ i, f i := by
  rw [← Finset.sum_image (fun i _ j _ h => e.injective h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => hf i)

omit [DecidableEq I] [DecidableEq J] in
lemma hsVector_submatrix_norm_sq_le {I' J' : Type*} [Fintype I'] [Fintype J']
    [DecidableEq I'] [DecidableEq J'] (e : I' ↪ I) (f : J' ↪ J) (M : Matrix I J ℂ) :
    ‖hsVector (M.submatrix e f)‖^2 ≤ ‖hsVector M‖^2 := by
  rw [hsVector_norm_sq_sum, hsVector_norm_sq_sum]
  calc
    _ ≤ ∑ i : I', ∑ j : J, ‖M (e i) j‖^2 := Finset.sum_le_sum fun i _ =>
      finite_sum_embedding_le f (fun j => ‖M (e i) j‖^2) (fun _ => sq_nonneg _)
    _ ≤ _ := finite_sum_embedding_le e (fun i => ∑ j, ‖M i j‖^2)
      (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The exact Hilbert--Schmidt trace formula used in the two PSD majorizations. -/
lemma hsVector_sandwich_sq (A B X : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖hsVector (A * X * B)‖^2 = (A^2 * X * B^2 * X.conjTranspose).trace.re := by
  rw [hsVector_norm_sq]
  simp only [Matrix.conjTranspose_mul, hA.eq, hB.eq]
  congr 1
  calc
    _ = ((B * X.conjTranspose) * (A*A*X*B)).trace := by
      simp only [mul_assoc]
    _ = ((A*A*X*B) * (B * X.conjTranspose)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [pow_two, mul_assoc]

/-- A concrete finite-algebra Hilbert--Schmidt core, not the operator norm. -/
@[instance_reducible]
def matrixAlgebraCore (A : StarSubalgebra ℂ (Matrix I I ℂ)) : InnerProductSpace.Core ℂ A where
  inner a b := inner ℂ (hsVector a.val) (hsVector b.val)
  conj_inner_symm a b := inner_conj_symm _ _
  re_inner_nonneg a := inner_self_nonneg
  add_left a b c := by
    change inner ℂ (hsVector (a.val + b.val)) (hsVector c.val) = _
    rw [map_add, inner_add_left]
  smul_left a b c := by
    change inner ℂ (hsVector (c • a.val)) (hsVector b.val) = _
    rw [map_smul, inner_smul_left]
  definite a h := Subtype.ext (hsVector_injective (by simpa using inner_self_eq_zero.mp h))

def matrixAlgebraTrace (A : StarSubalgebra ℂ (Matrix I I ℂ)) : A →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap I ℂ ℂ).comp A.subtype.toLinearMap

lemma matrixAlgebraCore_inner (A : StarSubalgebra ℂ (Matrix I I ℂ)) (a b : A) :
    (matrixAlgebraCore A).inner a b = matrixAlgebraTrace A (star a * b) := by
  exact hsVector_inner a.val b.val

instance matrixAlgebraIsClosed (A : StarSubalgebra ℂ (Matrix I I ℂ)) : IsClosed (A : Set (Matrix I I ℂ)) :=
  A.toSubalgebra.toSubmodule.closed_of_finiteDimensional

end RowColumn.MatrixState

end
end

end OAI
