import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RealDecode
import OAI.Analysis.MatrixSigning.Optimization.Affine

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N n m p : ℕ}

def valueDimension (d : ℕ) := 1+(d*d+d*d)

def valueIndex (d : ℕ) :
    Fin 1 ⊕ ((Fin d × Fin d) ⊕ (Fin d × Fin d)) ≃ Fin (valueDimension d) :=
  ((Equiv.refl (Fin 1)).sumCongr (finProdFinEquiv.sumCongr finProdFinEquiv)).trans
    (((Equiv.refl (Fin 1)).sumCongr finSumFinEquiv).trans finSumFinEquiv)

def timeCoordinate {R : Type*} [Semiring R] (d : ℕ) :
    (Fin (valueDimension d) → R) →ₗ[R] R := LinearMap.proj (valueIndex d (.inl 0))

def matrixCoordinate {R : Type*} [Semiring R] (d : ℕ) (second : Bool) :
    (Fin (valueDimension d) → R) →ₗ[R] (Fin d × Fin d → R) :=
  LinearMap.pi fun ij => LinearMap.proj (valueIndex d
    (.inr (if second then .inr ij else .inl ij)))

def realFinDecode {R : Type*} [CommRing R] (d : ℕ) :
    (Fin d × Fin d → R) →ₗ[R] Matrix (Fin (d+d)) (Fin (d+d)) R where
  toFun x := (realDecode x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  map_add' x y := by simp only [realDecode_add,Matrix.submatrix_add,Pi.add_apply]
  map_smul' r x := by simp only [realDecode_smul,Matrix.submatrix_smul,Pi.smul_apply,RingHom.id_apply]

lemma realFinDecode_symm {R : Type*} [CommRing R] (x : Fin d × Fin d → R) :
    (realFinDecode d x).IsSymm := (realDecode_isSymm x).submatrix _

def matrixVariable {R : Type*} [CommRing R] (d : ℕ) (second : Bool) :
    (Fin (valueDimension d) → R) →ₗ[R] Matrix (Fin (d+d)) (Fin (d+d)) R :=
  (realFinDecode d).comp (matrixCoordinate d second)

lemma matrixVariable_symm {R : Type*} [CommRing R] (second : Bool)
    (v : Fin (valueDimension d) → R) : (matrixVariable d second v).IsSymm :=
  realFinDecode_symm _

variable {R : Type*} [CommRing R]

def sandwichLinear (A : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m) (Fin m) R →ₗ[R] Matrix (Fin m) (Fin m) R where
  toFun Z := A*Z*A
  map_add' Z W := by simp only [mul_add,add_mul]
  map_smul' r Z := by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

lemma sandwichLinear_symm (A Z : Matrix (Fin m) (Fin m) R)
    (hA : A.IsSymm) (hZ : Z.IsSymm) : (sandwichLinear A Z).IsSymm := by
  change (A*Z*A).transpose=A*Z*A
  rw [Matrix.transpose_mul,Matrix.transpose_mul,hA,hZ,Matrix.mul_assoc]

def rationalSum (coords : Fin N → Fin d × Fin d → R) (x : Fin N → R) :
    Matrix (Fin (d+d)) (Fin (d+d)) R := ∑ i,x i • realFinDecode d (coords i)

lemma rationalSum_symm (coords : Fin N → Fin d × Fin d → R) (x : Fin N → R) :
    (rationalSum coords x).IsSymm := by
  change (∑ i,x i • realFinDecode d (coords i)).transpose= _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (realFinDecode_symm _).smul _

def rationalEta (coords : Fin N → Fin d × Fin d → R) (θ : Fin N → R) :
    Matrix (Fin (d+d)) (Fin (d+d)) R →ₗ[R] Matrix (Fin (d+d)) (Fin (d+d)) R :=
  ∑ i,(384*θ i) • sandwichLinear (realFinDecode d (coords i))

lemma rationalEta_symm (coords : Fin N → Fin d × Fin d → R) (θ : Fin N → R)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) R) (hZ : Z.IsSymm) :
    (rationalEta coords θ Z).IsSymm := by
  simp only [rationalEta,LinearMap.sum_apply,LinearMap.smul_apply]
  change (∑ i,(384*θ i) • (sandwichLinear (realFinDecode d (coords i)) Z)).transpose= _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (sandwichLinear_symm _ _ (realFinDecode_symm _) hZ).smul _

def identityLinear (m : ℕ) (L : (Fin n → R) →ₗ[R] R) :
    (Fin n → R) →ₗ[R] Matrix (Fin m) (Fin m) R where
  toFun v := L v • (1 : Matrix (Fin m) (Fin m) R)
  map_add' v w := by simp only [map_add,add_smul]
  map_smul' r v := by simp only [map_smul,RingHom.id_apply,smul_smul,smul_eq_mul]

def diagonalLinear (L : (Fin n → R) →ₗ[R] Matrix (Fin m) (Fin m) R)
    (K : (Fin n → R) →ₗ[R] Matrix (Fin p) (Fin p) R) :
    (Fin n → R) →ₗ[R] Matrix (Fin (m+p)) (Fin (m+p)) R where
  toFun v := blockDiagonal (L v) (K v)
  map_add' v w := by
    ext i j
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [blockDiagonal,hi,hj,Matrix.add_apply]
  map_smul' r v := by
    ext i j
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [blockDiagonal,hi,hj,Matrix.smul_apply]

def schurPencil (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) : Pencil (valueDimension d) ((d+d)+(d+d)) :=
  let S := if second then rationalSum coords x else -rationalSum coords x
  let C := (Matrix.fromBlocks S (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) 1 0).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  let L := diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
    (rationalEta coords θ).comp (matrixVariable d (!second))) (matrixVariable d second)
  Pencil.ofAffine C L
    ((Matrix.IsSymm.fromBlocks
      (by dsimp [S]; split
          · exact rationalSum_symm _ _
          · exact (rationalSum_symm _ _).neg)
      (by simp) (by simp)).submatrix _)
    (fun v => by
      apply blockDiagonal_symm
      · change (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-
          rationalEta coords θ (matrixVariable d (!second) v)).IsSymm
        exact (Matrix.isSymm_one.smul _).sub
          (rationalEta_symm coords θ _ (matrixVariable_symm _ _))
      · exact matrixVariable_symm _ _)

def lowerMatrixPencil (d : ℕ) (second : Bool) : Pencil (valueDimension d) (d+d) :=
  Pencil.ofAffine ((-1/400 : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ))
    (matrixVariable d second) (Matrix.isSymm_one.smul _) (matrixVariable_symm second)

def upperMatrixPencil (d : ℕ) (ε : ℚ) (second : Bool) : Pencil (valueDimension d) (d+d) :=
  Pencil.ofAffine ((200/ε : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ))
    (-(matrixVariable (R := ℚ) d second)) (Matrix.isSymm_one.smul _) (fun v => (matrixVariable_symm second v).neg)

def lowerTimePencil (d : ℕ) : Pencil (valueDimension d) 1 :=
  Pencil.ofAffine 0 (identityLinear 1 (timeCoordinate d)) (by simp) (fun _ => Matrix.isSymm_one.smul _)

def upperTimePencil (d : ℕ) : Pencil (valueDimension d) 1 :=
  Pencil.ofAffine ((100 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))
    (-(identityLinear (R := ℚ) 1 (timeCoordinate d))) (Matrix.isSymm_one.smul _)
    (fun _ => (Matrix.isSymm_one.smul _).neg)

def valuePencil (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :=
  (((((((schurPencil coords x θ false).blockDiagonal (schurPencil coords x θ true)).blockDiagonal
    (lowerMatrixPencil d false)).blockDiagonal (upperMatrixPencil d ε false)).blockDiagonal
    (lowerMatrixPencil d true)).blockDiagonal (upperMatrixPencil d ε true)).blockDiagonal
    (lowerTimePencil d)).blockDiagonal (upperTimePencil d)

def valueObjective (d : ℕ) (ε : ℚ) : (Fin (valueDimension d) → ℚ) →ₗ[ℚ] ℚ :=
  timeCoordinate d+ ε • (∑ i : Fin d, ((LinearMap.proj (i,i)).comp
    (matrixCoordinate d false)+(LinearMap.proj (i,i)).comp (matrixCoordinate d true)))

lemma schurPencil_eval (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (schurPencil coords x θ second).eval v =
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)+
        (if second then rationalSum coords x else -rationalSum coords x)-
        rationalEta coords θ (matrixVariable d (!second) v))
      1 1 (matrixVariable d second v)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  erw [schurPencil,Pencil.ofAffine_eval]
  ext i j
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [diagonalLinear,blockDiagonal,hi,hj,identityLinear,Matrix.add_apply,Matrix.sub_apply]
  abel

lemma lowerMatrixPencil_eval (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (lowerMatrixPencil d second).eval v = matrixVariable d second v-(1/400:ℚ) • 1 := by
  rw [lowerMatrixPencil,Pencil.ofAffine_eval]
  rw [neg_div,neg_smul]
  abel
lemma upperMatrixPencil_eval (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (upperMatrixPencil d ε second).eval v = (200/ε:ℚ) • 1-matrixVariable d second v := by
  rw [upperMatrixPencil,Pencil.ofAffine_eval]
  simp only [LinearMap.neg_apply,sub_eq_add_neg]
lemma valueObjective_apply (ε : ℚ) (v : Fin (valueDimension d) → ℚ) :
    valueObjective d ε v = timeCoordinate d v+ε*
      (∑ i : Fin d, (matrixCoordinate d false v (i,i)+matrixCoordinate d true v (i,i))) := by
  simp [valueObjective,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]

end CurrentKS.RationalSDP

end OAI
