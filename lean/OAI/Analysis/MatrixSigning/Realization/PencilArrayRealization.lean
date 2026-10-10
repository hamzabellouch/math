import Mathlib
import OAI.Analysis.MatrixSigning.Realization.VectorRealization
import OAI.Analysis.MatrixSigning.Optimization.Pencil

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

abbrev PencilData := MatrixData×List MatrixData
abbrev pencilCode := prodCode matrixCode (listCode matrixCode)

def accumMatrix (p : MatrixData×(ℚ×MatrixData)) : MatrixData :=
  zipDefault (zipDefault (fun r : ℚ×ℚ => r.1+r.2) 0 0) [] []
    (p.1,p.2.2.map (fun row => row.map (fun x => p.2.1*x)))

def accumMatrixRealizes : Realizes (prodCode matrixCode (prodCode ratCode matrixCode)) matrixCode accumMatrix :=
  let acc := first matrixCode (prodCode ratCode matrixCode)
  let new := (second matrixCode (prodCode ratCode matrixCode)).then matrixScale
  (acc.both new).then matrixAdd

def evalPencilData (p : PencilData×List ℚ) : MatrixData :=
  (zipDefault (id : ℚ×MatrixData → ℚ×MatrixData) 0 [] (p.2,p.1.2)).foldl
    (fun a b => accumMatrix (a,b)) p.1.1

def evalPencil : Realizes (prodCode pencilCode vectorCode) matrixCode evalPencilData :=
  let pencil := first pencilCode vectorCode
  let c := pencil.then (first matrixCode (listCode matrixCode))
  let bs := pencil.then (second matrixCode (listCode matrixCode))
  let y := second pencilCode vectorCode
  let pairs := (y.both bs).then ((identity (prodCode ratCode matrixCode)).zipWith 0 [])
  (c.both pairs).then accumMatrixRealizes.fold

def normalData (p : PencilData×List ℚ) : List ℚ :=
  p.1.2.map (fun m => -quadraticValue (p.2,m))

def normalPencil : Realizes (prodCode pencilCode vectorCode) vectorCode normalData :=
  let c := (first pencilCode vectorCode).then (second matrixCode (listCode matrixCode))
  let v := second pencilCode vectorCode
  (v.both c).then quadratic.neg.mapCtx

def pencilData {n m : ℕ} (B : RationalSDP.Pencil n m) : PencilData :=
  (matrixData B.constant,List.ofFn (fun i => matrixData (B.coeff i)))

lemma accumMatrix_data {m : ℕ} (A M : Matrix (Fin m) (Fin m) ℚ) (q : ℚ) :
    accumMatrix (matrixData A,(q,matrixData M))=matrixData (A+q • M) := by
  unfold accumMatrix
  rw [matrixScale_data,matrixAdd_data]

lemma fold_matrixData {m : ℕ} (xs : List (ℚ×Matrix (Fin m) (Fin m) ℚ))
    (A : Matrix (Fin m) (Fin m) ℚ) :
    (xs.map (fun p => (p.1,matrixData p.2))).foldl (fun a b => accumMatrix (a,b)) (matrixData A)=
      matrixData (A+(xs.map (fun p => p.1 • p.2)).sum) := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,accumMatrix_data,ih,List.sum_cons]
    rw [add_assoc]

lemma evalPencil_data {n m : ℕ} (B : RationalSDP.Pencil n m) (y : Fin n → ℚ) :
    evalPencilData (pencilData B,List.ofFn y)=matrixData (B.eval y) := by
  unfold evalPencilData pencilData
  rw [zipDefault_ofFn]
  have he : List.ofFn (fun i => (y i,matrixData (B.coeff i)))=
      (List.ofFn (fun i => (y i,B.coeff i))).map (fun p => (p.1,matrixData p.2)) := by
    simp only [List.map_ofFn,Function.comp_def]
  change (List.ofFn (fun i => (y i,matrixData (B.coeff i)))).foldl _ _=_
  rw [he,fold_matrixData]
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,RationalSDP.Pencil.eval]

lemma normalPencil_data {n m : ℕ} (B : RationalSDP.Pencil n m) (v : Fin m → ℚ) :
    normalData (pencilData B,List.ofFn v)=List.ofFn (B.normal v) := by
  simp only [normalData,pencilData,List.map_ofFn,Function.comp_def,quadratic_data]
  rfl

end CurrentKS.Realization

end

end OAI
