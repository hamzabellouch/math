import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.ValueDimension

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {n m p d N : ℕ}

lemma Pencil.ofAffine_realEval (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm)
    (L' : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hcast : ∀ y,(L y).map (fun q => (q:ℝ))=L' (fun i => (y i:ℝ))) (y : Fin n → ℝ) :
    (Pencil.ofAffine C L hC hL).realEval y=C.map (fun q => (q:ℝ))+L' y := by
  change _+∑ i,y i • (L (Pi.single i 1)).map (fun q => (q:ℝ))=_
  simp_rw [hcast]
  have hs (i : Fin n) : (fun j => ((Pi.single i 1 : Fin n → ℚ) j:ℝ))=Pi.single i 1 := by
    ext j
    simp [Pi.single_apply,apply_ite]
  simp_rw [hs]
  congr 1
  conv_rhs => rw [vector_eq_sum_single y]
  simp

lemma realFinDecode_cast (x : Fin d × Fin d → ℚ) :
    (realFinDecode d x).map (fun q => (q:ℝ))=realFinDecode d (fun i => (x i:ℝ)) := by
  change ((realDecode x).submatrix _ _).map _=(realDecode _).submatrix _ _
  rw [← Matrix.submatrix_map,realDecode_ratCast]

lemma matrixVariable_cast (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (matrixVariable d second v).map (fun q => (q:ℝ))=
      matrixVariable d second (fun i => (v i:ℝ)) := by
  change (realFinDecode d _).map _=realFinDecode d _
  rw [realFinDecode_cast]
  rfl

lemma cast_matrix_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin m) (Fin m) ℚ) :
    (∑ i ∈ s,A i).map (fun q => (q:ℝ))=∑ i ∈ s,(A i).map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.sum_apply,Rat.cast_sum]
lemma cast_matrix_smul (r : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) :
    (r • A).map (fun q => (q:ℝ))=(r:ℝ) • A.map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.smul_apply]
lemma cast_matrix_one : (1 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=1 := by
  exact Matrix.map_one _ (by simp) (by simp)
lemma cast_matrix_zero : (0 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=0 := by
  ext i j
  simp
lemma cast_matrix_add (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A+B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))+B.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_sub (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A-B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))-B.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_neg (A : Matrix (Fin m) (Fin m) ℚ) :
    (-A).map (fun q => (q:ℝ))= -A.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_mul (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A*B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))*B.map (fun q => (q:ℝ)) := by
  exact Matrix.map_mul (f := algebraMap ℚ ℝ)

lemma rationalSum_cast (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ) :
    (rationalSum coords x).map (fun q => (q:ℝ))=
      rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) := by
  simp only [rationalSum,cast_matrix_sum,cast_matrix_smul,realFinDecode_cast]

lemma rationalEta_cast (coords : Fin N → Fin d × Fin d → ℚ) (θ : Fin N → ℚ)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) :
    (rationalEta coords θ Z).map (fun q => (q:ℝ))=
      rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) (Z.map (fun q => (q:ℝ))) := by
  simp only [rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,cast_matrix_sum,
    cast_matrix_smul,sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk,cast_matrix_mul,
    realFinDecode_cast,Rat.cast_mul,Rat.cast_ofNat]

lemma schurPencil_realEval (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (schurPencil coords x θ second).realEval v =
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℝ)+
        (if second then rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
          else -rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))-
        rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) (matrixVariable d (!second) v))
      1 1 (matrixVariable d second v)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  let L' := diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
    (rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ))).comp
      (matrixVariable d (!second))) (matrixVariable d second)
  have hcast (y : Fin (valueDimension d) → ℚ) :
      (diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
        (rationalEta coords θ).comp (matrixVariable d (!second))) (matrixVariable d second) y).map
          (fun q => (q:ℝ))=L' (fun i => (y i:ℝ)) := by
    change (blockDiagonal _ _).map _=blockDiagonal _ _
    rw [blockDiagonal_realMap]
    congr 1
    · change ((timeCoordinate d y : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-rationalEta coords θ _).map _=_
      rw [cast_matrix_sub,cast_matrix_smul,cast_matrix_one,rationalEta_cast,matrixVariable_cast]
      rfl
    · exact matrixVariable_cast _ _
  erw [schurPencil,Pencil.ofAffine_realEval _ _ _ _ L' hcast]
  have hS : ((if second then rationalSum coords x else -rationalSum coords x).map
      (fun q => (q:ℝ))) = if second then rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
        else -rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) := by
    split <;> simp only [rationalSum_cast,cast_matrix_neg]
  ext i j
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [L',diagonalLinear,blockDiagonal,hi,hj,identityLinear,Matrix.add_apply,Matrix.sub_apply]
  · rename_i i' j'
    have hs := congrFun (congrFun hS i') j'
    change ((if second=true then rationalSum coords x else -rationalSum coords x) _ _ : ℝ)=_ at hs
    rw [hs]
    abel
  · simp [Matrix.one_apply,apply_ite]
  · simp [Matrix.one_apply,apply_ite]

end CurrentKS.RationalSDP

end OAI
