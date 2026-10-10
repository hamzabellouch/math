import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Coordinates
import OAI.Combinatorics.ThinTrees.Pencil.AffinePencil

namespace OAI

/-! Continuation pencil. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations RationalForms
open scoped BigOperators
variable {n m : ℕ}

abbrev Form (n m : ℕ) := Affine (dimension n m)

def qdiff (i j : Fin n) : Fin n → ℚ := Pi.single i 1-Pi.single j 1

def qlap (H : MultiGraph n m) : Matrix (Fin n) (Fin n) ℚ :=
  ∑e, vecMulVec (qdiff (H.left e) (H.right e)) (qdiff (H.left e) (H.right e))

def qtriangle (ijk : DistinctTriple n) : Matrix (Fin n) (Fin n) ℚ :=
  vecMulVec (qdiff ijk.1.1 ijk.1.2.1) (qdiff ijk.1.1 ijk.1.2.1)+
  vecMulVec (qdiff ijk.1.2.1 ijk.1.2.2) (qdiff ijk.1.2.1 ijk.1.2.2)-
  vecMulVec (qdiff ijk.1.1 ijk.1.2.2) (qdiff ijk.1.1 ijk.1.2.2)

def qproject (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := (1 : Matrix (Fin n) (Fin n) ℚ)-Matrix.of (fun (_ _ : Fin n) => (n:ℚ)⁻¹)

lemma cast_qdiff (i j k : Fin n) : (qdiff i j k : ℝ)=difference i j k := by
  simp only [qdiff, difference, point, Pi.sub_apply, Pi.single_apply, Rat.cast_sub]
  split_ifs <;> norm_num
lemma cast_qinc (H : MultiGraph n m) (e : Fin m) (i : Fin n) :
    (qdiff (H.left e) (H.right e) i : ℝ)=H.incidence e i := cast_qdiff _ _ _
lemma cast_qlap (H : MultiGraph n m) (i j : Fin n) : (qlap H i j : ℝ)=H.laplacian univ i j := by
  simp [qlap,laplacian,Matrix.sum_apply,Rat.cast_sum,vecMulVec,cast_qinc]
lemma cast_qtriangle (ijk : DistinctTriple n) (i j : Fin n) :
    (qtriangle ijk i j : ℝ)=triangleGenerator ijk i j := by
  simp [qtriangle,triangleGenerator,triangleMatrix,Matrix.sub_apply,vecMulVec,cast_qdiff]
lemma cast_qproject (i j : Fin n) : (qproject n i j : ℝ)=centering n i j := by
  change (((1 : Matrix (Fin n) (Fin n) ℚ) i j-(n:ℚ)⁻¹ : ℚ) : ℝ)=_
  simp only [centering,constantProjection,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec,Matrix.of_apply,ones,mul_one,Rat.cast_sub,Rat.cast_inv,Rat.cast_natCast,
    Matrix.one_apply]
  split_ifs <;> norm_num

def matrixForm (i j : Fin n) : Form n m :=
  ∑b, ∑a, (qproject n i a*qproject n b j/2) •
    (Affine.coord (matIndex a b)+Affine.coord (matIndex b a))

def lowerForm (H : MultiGraph n m) : Matrix (Fin n) (Fin n) (Form n m) :=
  fun i j => matrixForm i j-Affine.cst (qlap H i j)

def upperForm (H : MultiGraph n m) : Matrix (Fin n) (Fin n) (Form n m) :=
  fun i j => Affine.cst (3*qlap H i j)-matrixForm i j-
    ∑ijk : DistinctTriple n, (qtriangle ijk i j) • Affine.coord (mulIndex ijk.val)

def edgeForm (H : MultiGraph n m) (s : ℚ) (e : Fin m) : Matrix (Fin n) (Fin n) (Form n m) :=
  fun i j => matrixForm i j-
    (6*s*qdiff (H.left e) (H.right e) i*qdiff (H.left e) (H.right e) j) • Affine.coord (edgeIndex 0 e)

lemma real_matrixForm (v : Fin (dimension n m) → ℝ) (i j : Fin n) :
    Affine.real v (matrixForm i j)=(step v).matrix i j := by
  simp only [matrixForm,Affine.real_sum,Affine.real_smul,Affine.real_add,Affine.real_coord,
    Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,cast_qproject]
  simp only [step,StepFree.matrix,responseMatrix,centered,Matrix.mul_apply,
    Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,rawMatrix,smul_eq_mul,sum_mul]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

lemma real_lowerForm (H : MultiGraph n m) (v : Fin (dimension n m) → ℝ) :
    (lowerForm H).map (Affine.real v)=(step v).lowerPencil H := by
  ext i j
  simp [lowerForm,real_matrixForm,cast_qlap,StepFree.lowerPencil,Matrix.sub_apply]
lemma real_upperForm (H : MultiGraph n m) (v : Fin (dimension n m) → ℝ) :
    (upperForm H).map (Affine.real v)=(step v).upperPencil H := by
  ext i j
  simp only [Matrix.map_apply,upperForm,Affine.real_sub,Affine.real_cst,Affine.real_sum,
    Affine.real_smul,Affine.real_coord,real_matrixForm,Rat.cast_mul,Rat.cast_ofNat,cast_qlap,cast_qtriangle]
  simp only [StepFree.upperPencil,step,StepFree.multiplier,multiplier,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  congr 1
  apply sum_congr rfl
  intro ijk _
  ring
lemma real_edgeForm (H : MultiGraph n m) (s : ℚ) (e : Fin m) (v : Fin (dimension n m) → ℝ) :
    (edgeForm H s e).map (Affine.real v)=(step v).edgePencil H (s:ℝ) e := by
  ext i j
  simp [edgeForm,real_matrixForm,cast_qinc,StepFree.edgePencil,step,StepFree.y,y,
    Matrix.sub_apply,vecMulVec]
  ring

abbrev MatBlock (m : ℕ) := Fin 2 ⊕ Fin m

def matrixBlocks (H : MultiGraph n m) (s : ℚ) (u : Fin m → ℚ) :
    MatBlock m → Matrix (Fin n) (Fin n) (Form n m)
  | .inl p => if p=0 then lowerForm H else upperForm H
  | .inr e => if 0<u e then edgeForm H s e else 0

lemma matrixBlocks_symmetric (H : MultiGraph n m) (s : ℚ) (u : Fin m → ℚ) (b : MatBlock m) :
    (matrixBlocks H s u b).IsSymm := by
  apply symmetric_of_real
  intro v
  cases b with
  | inl p =>
    simp only [matrixBlocks]
    split_ifs
    · rw [real_lowerForm]
      exact isHermitian_iff_isSymm.mp (lowerPencil_hermitian H _)
    · rw [real_upperForm]
      exact isHermitian_iff_isSymm.mp (upperPencil_hermitian H _)
  | inr e =>
    simp only [matrixBlocks]
    split_ifs
    · rw [real_edgeForm]
      exact isHermitian_iff_isSymm.mp (edgePencil_hermitian H _ _ _)
    · simp

abbrev ScalarBlock (n m : ℕ) :=
  Triple n ⊕ ((Fin 7 × Fin m) ⊕ ((Fin 3 × (Fin n × Fin m)) ⊕ ((Fin n × Fin n) ⊕ Fin 1)))

def capacityForm (κ : ℚ) (u : Fin m → ℚ) (e : Fin m) : Form n m :=
  if 0<u e then Affine.coord (edgeIndex 1 e) else Affine.cst κ

def scalarForms (H : MultiGraph n m) (κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    ScalarBlock n m → Form n m
  | .inl ijk => if ijk.1≠ijk.2.1 ∧ ijk.2.1≠ijk.2.2 ∧ ijk.1≠ijk.2.2 then Affine.coord (mulIndex ijk) else 0
  | .inr (.inl (p,e)) =>
    ![Affine.coord (edgeIndex 0 e),Affine.cst 1-Affine.coord (edgeIndex 0 e),
      Affine.coord (edgeIndex 1 e),Affine.cst (κ+1)-Affine.coord (edgeIndex 1 e),
      if 0<u e then Affine.cst (κ+u e)-Affine.coord (edgeIndex 1 e)+
        t • ((5:ℚ) • Affine.coord (edgeIndex 0 e)-Affine.cst 4) else 0,
      Affine.coord (edgeIndex 2 e),capacityForm κ u e-Affine.coord (edgeIndex 2 e)] p
  | .inr (.inr (.inl (p,(r,e)))) =>
    ![Affine.coord (flowIndex 0 r e),Affine.coord (flowIndex 1 r e),
      Affine.coord (flowIndex 0 r e)+Affine.coord (flowIndex 1 r e)-Affine.coord (edgeIndex 2 e)] p
  | .inr (.inr (.inr (.inl (r,v)))) =>
    Affine.cst (if v=r then ε else qbar)-∑e,
      ((if H.left e=v then Affine.coord (flowIndex 0 r e) else 0)+
        (if H.right e=v then Affine.coord (flowIndex 1 r e) else 0))
  | .inr (.inr (.inr (.inr _))) =>
    (∑e, Affine.coord (edgeIndex 2 e))-Affine.cst (qbar*((n:ℚ)-1)-ε)

def order (n m : ℕ) := n*(2+m)+(n*(n*n)+(7*m+(3*(n*m)+(n*n+1))))

def rowIndex (n m : ℕ) : ((Fin n × MatBlock m) ⊕ ScalarBlock n m) ≃ Fin (order n m) :=
  let et : Triple n ≃ Fin (n*(n*n)) :=
    ((Equiv.refl (Fin n)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let ef : (Fin 3 × (Fin n × Fin m)) ≃ Fin (3*(n*m)) :=
    ((Equiv.refl (Fin 3)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  let eu := (finProdFinEquiv.sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv
  let ee := (finProdFinEquiv.sumCongr ((ef.sumCongr eu).trans finSumFinEquiv)).trans finSumFinEquiv
  let em := ((Equiv.refl (Fin n)).prodCongr finSumFinEquiv).trans finProdFinEquiv
  (em.sumCongr ((et.sumCongr ee).trans finSumFinEquiv)).trans finSumFinEquiv

def affineMatrix (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    Matrix (Fin (order n m)) (Fin (order n m)) (Form n m) :=
  (Matrix.fromBlocks (Matrix.blockDiagonal (matrixBlocks H s u)) 0 0
    (Matrix.diagonal (scalarForms H κ t qbar ε u))).submatrix (rowIndex n m).symm (rowIndex n m).symm

lemma affineMatrix_symmetric (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    (affineMatrix H s κ t qbar ε u).IsSymm := by
  apply IsSymm.submatrix
  apply IsSymm.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [Matrix.fromBlocks_apply₁₁,Matrix.blockDiagonal,Matrix.of_apply]
      by_cases h : i.2=j.2
      · simp only [h,ite_true]
        exact (matrixBlocks_symmetric H s u j.2).apply _ _
      · simp only [h,Ne.symm h,ite_false]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      exact (Matrix.isSymm_diagonal _).apply i j

def continuationPencil (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    CurrentKS.RationalSDP.Pencil (dimension n m) (order n m) :=
  pencil (affineMatrix H s κ t qbar ε u) (affineMatrix_symmetric H s κ t qbar ε u)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
