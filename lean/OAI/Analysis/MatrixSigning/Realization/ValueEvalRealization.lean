import Mathlib
import OAI.Analysis.MatrixSigning.Realization.PencilCompileRealization
import OAI.Analysis.MatrixSigning.Realization.ValueDataRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

abbrev ValueEvalData := ValueData×List ℚ
abbrev valueEvalCode := prodCode valueDataCode vectorCode
def veP := first valueDataCode vectorCode
def veY := second valueDataCode vectorCode
def veD := veP.then vdD
def veN := veD.then realDimension
def veEye := veN.then identityMatrix
def veEps := veP.then vdEps

def veTime : Realizes valueEvalCode ratCode (fun p => p.2.getD 0 0) :=
  ((constant valueEvalCode natCode 0).both veY).then (getD ratCode 0)
def veVariable (second : Bool) := (veD.both veY).then (matrixVariable second)

def sumData (p : ValueData) : MatrixData := weightedSumData (p.1+p.1,(p.2.2.1,p.2.1))
def veSum : Realizes valueEvalCode matrixCode (fun p => sumData p.1) :=
  (veN.both ((veP.then vdX).both (veP.then vdAtoms))).then weightedSum
lemma sumData_value {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :
    sumData (valueData coords x θ ε)=matrixData (RationalSDP.rationalSum coords x) := by
  apply weightedSum_data

def etaData (p : ValueData×MatrixData) : MatrixData :=
  weightedSumData (p.1.1+p.1.1,(p.1.2.2.2.1.map (fun z => 384*z),
    p.1.2.1.map (fun A => sandwichData (A,p.2))))
def eta : Realizes (prodCode valueDataCode matrixCode) matrixCode etaData :=
  let p := first valueDataCode matrixCode
  let Z := second valueDataCode matrixCode
  let n := (p.then vdD).then realDimension
  let weights := (p.then vdTheta).then ((constant ratCode ratCode 384).mul (identity ratCode)).map
  let atomSandwich := ((second matrixCode matrixCode).both (first matrixCode matrixCode)).then sandwich
  let atoms := (Z.both (p.then vdAtoms)).then atomSandwich.mapCtx
  (n.both (weights.both atoms)).then weightedSum
lemma etaData_value {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) :
    etaData (valueData coords x θ ε,matrixData Z)=matrixData (RationalSDP.rationalEta coords θ Z) := by
  unfold etaData valueData
  simp only [List.map_ofFn,Function.comp_def,sandwich_data]
  rw [weightedSum_data]
  simp only [RationalSDP.rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,RationalSDP.sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk]

def matrixAddData (p : MatrixData×MatrixData) :=
  zipDefault (zipDefault (fun q : ℚ×ℚ => q.1+q.2) 0 0) [] [] p
def matrixScaleData (p : ℚ×MatrixData) := p.2.map (fun row => row.map (fun x => p.1*x))
def eyeData (n : ℕ) := (List.range n).map (fun i => (List.range n).map (fun j => if i=j then (1:ℚ) else 0))

def schurEvalData (second : Bool) (p : ValueEvalData) : MatrixData :=
  let I := eyeData (p.1.1+p.1.1)
  let S := if second then sumData p.1 else matrixNegData (sumData p.1)
  let etaZ := etaData (p.1,matrixVariableData (!second) (p.1.1,p.2))
  let top := matrixSubData (matrixAddData (matrixScaleData (p.2.getD 0 0,I),S),etaZ)
  fromBlocksData ((top,I),(I,matrixVariableData second (p.1.1,p.2)))
def schurEval (second : Bool) : Realizes valueEvalCode matrixCode (schurEvalData second) :=
  let S := (constant valueEvalCode boolCode second).ite veSum (veSum.then negateMatrix)
  let etaZ := (veP.both (veVariable (!second))).then eta
  let top := (((veTime.scaleMatrix veEye).both S).then matrixAdd).both etaZ |>.then matrixSub
  ((top.both veEye).both (veEye.both (veVariable second))).then fromBlocks

lemma time_getD {d : ℕ} (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    (List.ofFn y).getD 0 0=RationalSDP.timeCoordinate d y := by
  have h : (RationalSDP.valueIndex d (.inl 0)).val=0 := rfl
  rw [← h,getD_ofFn]
  rfl

lemma schurEval_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    schurEvalData second (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.schurPencil coords x θ second).eval y) := by
  have hd : (valueData coords x θ ε).1=d := rfl
  cases second <;> simp only [schurEvalData,hd,eyeData,identityMatrix_data,
    matrixVariable_data,time_getD,sumData_value,etaData_value,Bool.false_eq_true,ite_false,ite_true,
    matrixNeg_data,matrixScaleData,matrixScale_data,matrixAddData,matrixAdd_data,
    matrixSub_data,fromBlocks_data]
  all_goals rw [RationalSDP.schurPencil_eval];rfl

def lowerBoxData (second : Bool) (p : ValueEvalData) : MatrixData :=
  matrixSubData (matrixVariableData second (p.1.1,p.2),matrixScaleData (1/400,eyeData (p.1.1+p.1.1)))
def lowerBox (second : Bool) : Realizes valueEvalCode matrixCode (lowerBoxData second) :=
  ((veVariable second).both ((constant valueEvalCode ratCode (1/400)).scaleMatrix veEye)).then matrixSub

def upperBoxData (second : Bool) (p : ValueEvalData) : MatrixData :=
  matrixSubData (matrixScaleData (200/p.1.2.2.2.2,eyeData (p.1.1+p.1.1)),matrixVariableData second (p.1.1,p.2))
def upperBox (second : Bool) : Realizes valueEvalCode matrixCode (upperBoxData second) :=
  ((((constant valueEvalCode ratCode 200).div veEps).scaleMatrix veEye).both (veVariable second)).then matrixSub

def tinyMatrix : Realizes ratCode matrixCode (fun q => [[q]]) :=
  (singletonList ratCode).then (singletonList vectorCode)
lemma tinyMatrix_data (q : ℚ) : [[q]]=matrixData (q • (1 : Matrix (Fin 1) (Fin 1) ℚ)) := by
  simp [matrixData,List.ofFn_succ]

def valueEvalData (p : ValueEvalData) : MatrixData :=
  blockDiagonalData (blockDiagonalData (blockDiagonalData (blockDiagonalData (blockDiagonalData
    (blockDiagonalData (blockDiagonalData (schurEvalData false p,schurEvalData true p),
      lowerBoxData false p),upperBoxData false p),lowerBoxData true p),upperBoxData true p),
        [[p.2.getD 0 0]]),[[100-p.2.getD 0 0]])

def Realizes.blockWith {α : Type*} {ea : α → Word} {f g : α → MatrixData}
    (r : Realizes ea matrixCode f) (s : Realizes ea matrixCode g) :
    Realizes ea matrixCode (fun p => blockDiagonalData (f p,g p)) := (r.both s).then blockDiagonal

def valueEval : Realizes valueEvalCode matrixCode valueEvalData :=
  (((((((schurEval false).blockWith (schurEval true)).blockWith (lowerBox false)).blockWith
    (upperBox false)).blockWith (lowerBox true)).blockWith (upperBox true)).blockWith
    (veTime.then tinyMatrix)).blockWith (((constant valueEvalCode ratCode 100).sub veTime).then tinyMatrix)

lemma lowerBox_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    lowerBoxData second (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.lowerMatrixPencil d second).eval y) := by
  unfold lowerBoxData
  change matrixSubData (matrixVariableData second (d,List.ofFn y),matrixScaleData (1/400,eyeData (d+d)))=_
  rw [matrixVariable_data,eyeData,identityMatrix_data,matrixScaleData,matrixScale_data,matrixSub_data,
    RationalSDP.lowerMatrixPencil_eval]
lemma upperBox_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    upperBoxData second (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.upperMatrixPencil d ε second).eval y) := by
  unfold upperBoxData
  change matrixSubData (matrixScaleData (200/ε,eyeData (d+d)),matrixVariableData second (d,List.ofFn y))=_
  rw [matrixVariable_data,eyeData,identityMatrix_data,matrixScaleData,matrixScale_data,matrixSub_data,
    RationalSDP.upperMatrixPencil_eval]

lemma pencil_blockDiagonal_eval {n m p : ℕ} (A : RationalSDP.Pencil n m) (B : RationalSDP.Pencil n p)
    (z : Fin n → ℚ) : (A.blockDiagonal B).eval z=RationalSDP.blockDiagonal (A.eval z) (B.eval z) := by
  ext i j
  simp only [RationalSDP.Pencil.eval,RationalSDP.Pencil.blockDiagonal,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [RationalSDP.blockDiagonal,hi,hj,Matrix.sum_apply]

lemma valueEval_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    valueEvalData (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.valuePencil coords x θ ε).eval y) := by
  unfold valueEvalData
  rw [schurEval_data,schurEval_data,lowerBox_data,lowerBox_data,upperBox_data,upperBox_data,time_getD]
  simp only [tinyMatrix_data,blockDiagonal_data,RationalSDP.valuePencil,pencil_blockDiagonal_eval]
  congr 1
  have hl : (RationalSDP.lowerTimePencil d).eval y=RationalSDP.timeCoordinate d y •
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    erw [RationalSDP.lowerTimePencil,RationalSDP.Pencil.ofAffine_eval,zero_add];rfl
  have hu : (RationalSDP.upperTimePencil d).eval y=(100-RationalSDP.timeCoordinate d y) •
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    erw [RationalSDP.upperTimePencil,RationalSDP.Pencil.ofAffine_eval]
    change (100:ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) + -(RationalSDP.timeCoordinate d y • (1 : Matrix (Fin 1) (Fin 1) ℚ)) = _
    rw [← sub_eq_add_neg,← sub_smul]
  rw [hl,hu]

end CurrentKS.Realization

end OAI
