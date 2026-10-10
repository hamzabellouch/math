import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RealifyHermitian
import OAI.Analysis.MatrixSigning.Arithmetic.RealifyAdd
import OAI.Analysis.MatrixSigning.Optimization.AffineRealEval

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates KS.W08
open scoped BigOperators ComplexOrder

variable {n m p d N : ℕ}

lemma lowerMatrixPencil_realEval (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (lowerMatrixPencil d second).realEval v = matrixVariable d second v-(1/400:ℝ) • 1 := by
  rw [lowerMatrixPencil,Pencil.ofAffine_realEval _ _ _ _ (matrixVariable d second)
    (matrixVariable_cast second),cast_matrix_smul,cast_matrix_one]
  norm_num
  abel
lemma upperMatrixPencil_realEval (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (upperMatrixPencil d ε second).realEval v = (200/(ε:ℝ)) • 1-matrixVariable d second v := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      ((-(matrixVariable (R := ℚ) d second)) y).map (fun q => (q:ℝ))=
        (-(matrixVariable (R := ℝ) d second)) (fun i => (y i:ℝ)) := by
    simp only [LinearMap.neg_apply,cast_matrix_neg,matrixVariable_cast]
  erw [upperMatrixPencil,Pencil.ofAffine_realEval _ _ _ _ (-(matrixVariable (R := ℝ) d second)) hc,
    cast_matrix_smul,cast_matrix_one]
  simp only [Rat.cast_div,Rat.cast_ofNat,LinearMap.neg_apply,sub_eq_add_neg]
lemma lowerTimePencil_realEval (v : Fin (valueDimension d) → ℝ) :
    (lowerTimePencil d).realEval v=timeCoordinate d v • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      (identityLinear 1 (timeCoordinate d) y).map (fun q => (q:ℝ))=
        identityLinear 1 (timeCoordinate d) (fun i => (y i:ℝ)) := by
    change ((timeCoordinate d y : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)).map _=_
    rw [cast_matrix_smul,cast_matrix_one]
    rfl
  erw [lowerTimePencil,Pencil.ofAffine_realEval _ _ _ _ (identityLinear 1 (timeCoordinate d)) hc,
    cast_matrix_zero,zero_add]
  rfl
lemma upperTimePencil_realEval (v : Fin (valueDimension d) → ℝ) :
    (upperTimePencil d).realEval v=(100-timeCoordinate d v) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      ((-(identityLinear (R := ℚ) 1 (timeCoordinate d))) y).map (fun q => (q:ℝ))=
        (-(identityLinear (R := ℝ) 1 (timeCoordinate d))) (fun i => (y i:ℝ)) := by
    change (-((timeCoordinate d y : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))).map _=_
    rw [cast_matrix_neg,cast_matrix_smul,cast_matrix_one]
    rfl
  erw [upperTimePencil,Pencil.ofAffine_realEval _ _ _ _ (-(identityLinear (R := ℝ) 1 (timeCoordinate d))) hc,
    cast_matrix_smul,cast_matrix_one]
  norm_num only [Rat.cast_ofNat]
  change (100:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) + -(timeCoordinate d v • 1)=_
  module

lemma posSemidef_reindex_iff {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (e : β ≃ α) : (A.submatrix e e).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.submatrix e.symm
    simp only [Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply] at hh
    exact hh
  · exact fun h => h.submatrix _

noncomputable def finRealify (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  (realify A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

lemma finRealify_psd (A : Matrix (Fin d) (Fin d) ℂ) :
    (finRealify A).PosSemidef ↔ A.PosSemidef := by
  rw [finRealify,posSemidef_reindex_iff,realify_posSemidef_iff]
lemma finRealify_decode (x : Fin d × Fin d → ℝ) : finRealify (decode x)=realFinDecode d x := by
  unfold finRealify
  rw [← realDecode_eq_realify]
  rfl
lemma finRealify_one : finRealify (1 : Matrix (Fin d) (Fin d) ℂ)=1 := by
  unfold finRealify
  rw [realify_one]
  ext i j
  simp [Matrix.one_apply]
lemma finRealify_add (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A+B)=finRealify A+finRealify B := by
  simp only [finRealify,realify_add,Matrix.submatrix_add,Pi.add_apply]
lemma finRealify_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (r • A)=r • finRealify A := by
  simp only [finRealify,realify_smul,Matrix.submatrix_smul,Pi.smul_apply]
lemma finRealify_neg (A : Matrix (Fin d) (Fin d) ℂ) : finRealify (-A)= -finRealify A := by
  have h : realify (-A) = -realify A := by
    ext (i|i) (j|j) <;> simp [realify,Matrix.fromBlocks]
  simp only [finRealify,h,Matrix.submatrix_neg]
  rfl
lemma finRealify_sub (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A-B)=finRealify A-finRealify B := by
  simp only [sub_eq_add_neg,finRealify_add,finRealify_neg]
lemma finRealify_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A*B)=finRealify A*finRealify B := by
  rw [finRealify,realify_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _).symm
lemma finRealify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    finRealify (∑ i ∈ s,A i)=∑ i ∈ s,finRealify (A i) := by
  ext i j
  simp only [finRealify,realify_sum,Matrix.submatrix_apply,Matrix.sum_apply]

lemma realify_schur (T X : Matrix (Fin d) (Fin d) ℂ) :
    (realify (Matrix.fromBlocks T 1 1 X)).submatrix
      (Equiv.sumSumSumComm (Fin d) (Fin d) (Fin d) (Fin d))
      (Equiv.sumSumSumComm (Fin d) (Fin d) (Fin d) (Fin d))=
    Matrix.fromBlocks (realify T) 1 1 (realify X) := by
  ext i j
  rcases i with i | i <;> rcases i with i | i <;>
    rcases j with j | j <;> rcases j with j | j <;>
    simp [realify,Matrix.fromBlocks,Equiv.sumSumSumComm,Matrix.one_apply,apply_ite]

lemma finRealify_schur_psd (T X : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.fromBlocks (finRealify T) 1 1 (finRealify X)).PosSemidef ↔
      (Matrix.fromBlocks T (1 : Matrix (Fin d) (Fin d) ℂ) 1 X).PosSemidef := by
  let e := (finSumFinEquiv.symm : Fin (d+d) ≃ Fin d ⊕ Fin d).sumCongr
    (finSumFinEquiv.symm : Fin (d+d) ≃ Fin d ⊕ Fin d)
  have he : Matrix.fromBlocks (finRealify T) 1 1 (finRealify X)=
      (Matrix.fromBlocks (realify T) 1 1 (realify X)).submatrix e e := by
    ext i j
    cases i <;> cases j <;> simp [finRealify,e,Matrix.one_apply]
  rw [he,posSemidef_reindex_iff,← realify_schur,posSemidef_reindex_iff,realify_posSemidef_iff]

noncomputable def complexSum (coords : Fin N → Fin d × Fin d → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ i,x i • decode (coords i)
noncomputable def complexEta (coords : Fin N → Fin d × Fin d → ℝ) (θ : Fin N → ℝ)
    (Z : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i,(384*θ i) • (decode (coords i)*Z*decode (coords i))
lemma finRealify_complexSum (coords : Fin N → Fin d × Fin d → ℝ) (x : Fin N → ℝ) :
    finRealify (complexSum coords x)=rationalSum coords x := by
  simp only [complexSum,finRealify_sum,finRealify_smul,finRealify_decode,rationalSum]
lemma finRealify_complexEta (coords : Fin N → Fin d × Fin d → ℝ) (θ : Fin N → ℝ)
    (Z : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (complexEta coords θ Z)=rationalEta coords θ (finRealify Z) := by
  simp only [complexEta,finRealify_sum,finRealify_smul,finRealify_mul,finRealify_decode,
    rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk]

lemma schurPencil_psd (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((schurPencil coords x θ second).realEval v).PosSemidef ↔
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin d) (Fin d) ℂ)+
        (if second then complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
          else -complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))-
        complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ))
          (decode (matrixCoordinate d (!second) v)))
      1 1 (decode (matrixCoordinate d second v))).PosSemidef := by
  rw [schurPencil_realEval,posSemidef_reindex_iff,← finRealify_schur_psd]
  simp only [finRealify_sub,finRealify_add,finRealify_smul,finRealify_one,
    finRealify_complexEta,finRealify_decode]
  split <;> simp only [finRealify_complexSum,finRealify_neg,matrixVariable,LinearMap.comp_apply]

end CurrentKS.RationalSDP

end OAI
