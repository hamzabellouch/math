import Mathlib
import OAI.Analysis.MatrixSigning.Realization.LevelPencilRealization
import OAI.Analysis.MatrixSigning.Realization.CoordinateRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixNegData (A : MatrixData) := A.map (fun row => row.map (fun x => -x))
def matrixSubData (p : MatrixData×MatrixData) : MatrixData :=
  zipDefault (zipDefault (fun q : ℚ×ℚ => q.1+q.2) 0 0) [] [] (p.1,matrixNegData p.2)
def matrixSub : Realizes (prodCode matrixCode matrixCode) matrixCode matrixSubData :=
  ((first matrixCode matrixCode).both ((second matrixCode matrixCode).then negateMatrix)).then matrixAdd
lemma matrixNeg_data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixNegData (matrixData A)=matrixData (-A) := by
  simp only [matrixNegData,matrixData,List.map_ofFn,Function.comp_def];rfl
lemma matrixSub_data {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    matrixSubData (matrixData A,matrixData B)=matrixData (A-B) := by
  rw [matrixSubData,matrixNeg_data,matrixAdd_data,sub_eq_add_neg]

def zeroRect : Realizes (prodCode natCode natCode) matrixCode
    (fun p => List.replicate p.1 (List.replicate p.2 (0:ℚ))) :=
  let n := first natCode natCode
  let m := second natCode natCode
  let row := ((constant _ ratCode 0).both m).then (replicateList ratCode)
  (row.both n).then (replicateList vectorCode)

lemma zeroRect_data (n m : ℕ) :
    List.replicate n (List.replicate m (0:ℚ))=matrixData (0 : Matrix (Fin n) (Fin m) ℚ) := by
  change _=List.ofFn (fun _ : Fin n => List.ofFn (fun _ : Fin m => (0:ℚ)))
  simp

def blockDiagonalData (p : MatrixData×MatrixData) : MatrixData :=
  fromBlocksData ((p.1,List.replicate p.1.length (List.replicate p.2.length 0)),
    (List.replicate p.2.length (List.replicate p.1.length 0),p.2))
def blockDiagonal : Realizes (prodCode matrixCode matrixCode) matrixCode blockDiagonalData :=
  let A := first matrixCode matrixCode
  let B := second matrixCode matrixCode
  let n := A.then (lengthList vectorCode)
  let m := B.then (lengthList vectorCode)
  ((A.both ((n.both m).then zeroRect)).both (((m.both n).then zeroRect).both B)).then fromBlocks
lemma blockDiagonal_data {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ) :
    blockDiagonalData (matrixData A,matrixData B)=matrixData (RationalSDP.blockDiagonal A B) := by
  unfold blockDiagonalData
  simp only [matrixData,List.length_ofFn]
  change fromBlocksData ((matrixData A,_),(_,matrixData B))=_
  rw [zeroRect_data,zeroRect_data,fromBlocks_data]
  rfl

def basisData (p : ℕ×ℕ) : List ℚ := (List.range p.1).map (fun j => if p.2=j then 1 else 0)
def basisVector : Realizes (prodCode natCode natCode) vectorCode basisData :=
  ((second natCode natCode).both (first natCode natCode)).then identityEntry.tabulate
lemma basis_data {n : ℕ} (i : Fin n) : basisData (n,i.val)=List.ofFn (Pi.single i (1:ℚ)) := by
  rw [basisData,range_map_fin]
  apply congrArg List.ofFn
  funext j
  simp [Pi.single_apply,Fin.ext_iff,eq_comm]

variable {α : Type*}
def pencilFromEvalData (f : α×List ℚ → MatrixData) (p : α×ℕ) : PencilData :=
  let c := f (p.1,List.replicate p.2 0)
  (c,(List.range p.2).map (fun i => matrixSubData (f (p.1,basisData (p.2,i)),c)))

def Realizes.pencilFromEval {ea : α → Word} {f : α×List ℚ → MatrixData}
    (r : Realizes (prodCode ea vectorCode) matrixCode f) :
    Realizes (prodCode ea natCode) pencilCode (pencilFromEvalData f) :=
  let pc := prodCode ea natCode
  let a := first ea natCode
  let n := second ea natCode
  let zeros := ((constant pc ratCode 0).both n).then (replicateList ratCode)
  let c := (a.both zeros).then r
  let p := first pc natCode
  let idx := second pc natCode
  let ni := (p.then n).both idx
  let atBasis := ((p.then a).both (ni.then basisVector)).then r
  let one := (atBasis.both (p.then c)).then matrixSub
  c.both (((identity pc).both n).then one.tabulate)

lemma pencilFromEval_data {n m : ℕ} (B : RationalSDP.Pencil n m)
    (f : α×List ℚ → MatrixData) (a : α)
    (h : ∀ y : Fin n → ℚ,f (a,List.ofFn y)=matrixData (B.eval y)) :
    pencilFromEvalData f (a,n)=pencilData B := by
  have hc : f (a,List.replicate n 0)=matrixData B.constant := by
    simpa [RationalSDP.Pencil.eval,Pi.zero_def] using h 0
  unfold pencilFromEvalData
  simp only [hc]
  rw [range_map_fin]
  unfold pencilData
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [basis_data,h,matrixSub_data]
  congr 1
  simp [RationalSDP.Pencil.eval,Pi.single_apply]

end CurrentKS.Realization

end

end OAI
