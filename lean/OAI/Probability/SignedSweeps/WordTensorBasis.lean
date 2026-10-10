import OAI.Probability.SignedSweeps.TensorDensity
import OAI.Probability.SignedSweeps.SignedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) wordTensorBasisDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

abbrev colorHilbert (C : Type) [Fintype C] : FiniteComplexHilbert :=
  ⟨EuclideanSpace ℂ C, inferInstance, inferInstance, inferInstance⟩

def wordConsEquiv (C : Type*) (p : ℕ) : C × (Fin p → C) ≃ (Fin (p+1) → C) where
  toFun a := Fin.cons a.1 a.2
  invFun w := (w 0, fun i => w i.succ)
  left_inv a := by cases a; rfl
  right_inv w := by ext i; exact Fin.cases rfl (fun _ => rfl) i

def wordTensorBasis (C : Type) [Fintype C] : (p : ℕ) →
    OrthonormalBasis (Fin p → C) ℂ (tensorHilbertPower (colorHilbert C) p)
  | 0 => (OrthonormalBasis.singleton PUnit.{1} ℂ).reindex (Equiv.ofUnique _ _)
  | p+1 => ((EuclideanSpace.basisFun C ℂ).tensorProduct (wordTensorBasis C p)).reindex
      (wordConsEquiv C p)

lemma wordTensorBasis_zero (C : Type) [Fintype C] (w : Fin 0 → C) :
    wordTensorBasis C 0 w = (1 : ℂ) := by
  change ((OrthonormalBasis.singleton PUnit.{1} ℂ).reindex (Equiv.ofUnique _ _)) w = 1
  simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.singleton_apply]

lemma wordTensorBasis_succ (C : Type) [Fintype C] (p : ℕ) (w : Fin (p+1) → C) :
    wordTensorBasis C (p+1) w = EuclideanSpace.single (w 0) 1 ⊗ₜ[ℂ]
      wordTensorBasis C p (fun i => w i.succ) := by
  change (((EuclideanSpace.basisFun C ℂ).tensorProduct (wordTensorBasis C p)).reindex
    (wordConsEquiv C p)) w = _
  rw [OrthonormalBasis.reindex_apply,
    OrthonormalBasis.tensorProduct_apply, EuclideanSpace.basisFun_apply]
  rfl

def varyingWordTensor {p : ℕ} {C : Type*} (A : Fin p → Matrix C C ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ := fun w z => ∏ i, A i (w i) (z i)

lemma varyingWordTensor_const (p : ℕ) {C : Type*} (A : Matrix C C ℂ) :
    varyingWordTensor (fun _ : Fin p => A) = wordTensorMatrix p A := rfl

lemma wordTensorBasis_matrix {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ C) :
    LinearMap.toMatrixOrthonormal (wordTensorBasis C p) (tensorOperator (colorHilbert C) A) =
      varyingWordTensor (fun i => LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun C ℂ) (A i)) := by
  ext w z
  simp only [LinearMap.toMatrixOrthonormal_apply_apply, varyingWordTensor]
  induction p with
  | zero =>
    simp only [tensorOperator, wordTensorBasis_zero, Fin.prod_univ_zero]
    change inner ℂ (1 : ℂ) 1 = 1
    norm_num
  | succ p ih =>
    rw [wordTensorBasis_succ, wordTensorBasis_succ]
    change inner ℂ (_ ⊗ₜ[ℂ] _) (TensorProduct.map (A 0)
      (tensorOperator (colorHilbert C) (fun i : Fin p => A i.succ)) (_ ⊗ₜ[ℂ] _)) = _
    rw [TensorProduct.map_tmul, TensorProduct.inner_tmul, Fin.prod_univ_succ]
    rw [ih]
    rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) isometricConjWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

def isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) : F →ₗ[ℂ] F :=
  e.toLinearEquiv.conj A

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
@[simp] lemma isometricConj_apply [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    isometricConj e A x = e (A (e.symm x)) := rfl

lemma isometricConj_eq_block (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    isometricConj e A = hilbertBlock e.toLinearIsometry A := by
  change e.toLinearMap ∘ₗ A ∘ₗ e.symm.toLinearMap =
    e.toLinearMap ∘ₗ A ∘ₗ e.toLinearMap.adjoint
  rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

lemma isometricConj_positive (e : E ≃ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsPositive) :
    (isometricConj e A).IsPositive := by
  rw [isometricConj_eq_block]
  exact hilbertBlock_positive _ hA

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
lemma isometricConj_mul [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (A B : E →ₗ[ℂ] E) :
    isometricConj e (A * B) = isometricConj e A * isometricConj e B := by
  ext x
  simp only [Module.End.mul_apply, isometricConj_apply, LinearIsometryEquiv.symm_apply_apply]

lemma isometricConj_norm (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    ‖(isometricConj e A).toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖e (A (e.symm x))‖ ≤ _
    rw [e.norm_map]
    have hh := A.toContinuousLinearMap.le_opNorm (e.symm x)
    change ‖A (e.symm x)‖ ≤ ‖A.toContinuousLinearMap‖ * ‖e.symm x‖ at hh
    rw [e.symm.norm_map] at hh
    exact hh
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hh := (isometricConj e A).toContinuousLinearMap.le_opNorm (e x)
    change ‖e (A (e.symm (e x)))‖ ≤ _ at hh
    change ‖A x‖ ≤ _
    simpa only [e.symm_apply_apply, e.norm_map] using hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) orthonormalMatrixWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

lemma orthonormal_matrix_conjugate {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (b : OrthonormalBasis I ℂ E) (A : E →ₗ[ℂ] E) :
    (LinearMap.toMatrixOrthonormal b A).toEuclideanLin = isometricConj b.repr A := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro j
  change (LinearMap.toMatrixOrthonormal b A).toEuclideanLin (EuclideanSpace.single i 1) j =
    b.repr (A (b.repr.symm (EuclideanSpace.single i 1))) j
  rw [euclideanMatrix_single, LinearMap.toMatrixOrthonormal_apply_apply,
    OrthonormalBasis.repr_symm_single, OrthonormalBasis.repr_apply_apply]

lemma matrix_orthonormal_coordinates {C : Type*} [Fintype C]
    (A : Matrix C C ℂ) :
    LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun C ℂ) A.toEuclideanLin = A := by
  ext i j
  simp only [LinearMap.toMatrixOrthonormal_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, euclideanMatrix_single]

lemma varyingWordTensor_conjugate {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → Matrix C C ℂ) :
    (varyingWordTensor A).toEuclideanLin =
      isometricConj (wordTensorBasis C p).repr
        (tensorOperator (colorHilbert C) (fun i => (A i).toEuclideanLin)) := by
  have hm := wordTensorBasis_matrix (fun i => (A i).toEuclideanLin)
  simp only [matrix_orthonormal_coordinates] at hm
  rw [← hm]
  exact orthonormal_matrix_conjugate _ _

lemma varyingWordTensor_positive {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → Matrix C C ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (varyingWordTensor A).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  rw [varyingWordTensor_conjugate]
  exact isometricConj_positive _ (tensorOperator_positive _ _
    (fun i => Matrix.isPositive_toEuclideanLin_iff.mpr (hA i)))

lemma varyingWordTensor_norm_sq_le {C : Type} [Fintype C] {p : ℕ}
    (A : Fin p → Matrix C C ℂ) :
    ‖(varyingWordTensor A).toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤
      ∏ i, ‖(A i).toEuclideanLin.toContinuousLinearMap‖ ^ 2 := by
  rw [varyingWordTensor_conjugate, isometricConj_norm]
  exact tensorOperator_norm_sq_le _ _

end SignedSweeps
end

end OAI
