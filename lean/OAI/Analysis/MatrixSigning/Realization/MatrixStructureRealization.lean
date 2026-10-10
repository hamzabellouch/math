import Mathlib
import OAI.Analysis.MatrixSigning.Realization.VectorRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def natLE : Realizes (prodCode natCode natCode) boolCode (fun p => decide (p.1≤p.2)) :=
  (((first natCode natCode).then natToRat).le ((second natCode natCode).then natToRat)).congr
    (by intro p;simp)

def natEq : Realizes (prodCode natCode natCode) boolCode (fun p => decide (p.1=p.2)) :=
  let rev := (second natCode natCode).both (first natCode natCode)
  (natLE.ite (rev.then natLE) (constant (prodCode natCode natCode) boolCode false)).congr
    (by intro p;by_cases h : p.1≤p.2 <;> by_cases k : p.2≤p.1 <;> by_cases e : p.1=p.2 <;> simp_all; omega)

def matrixEntry : Realizes (prodCode matrixCode (prodCode natCode natCode)) ratCode
    (fun p => (p.1.getD p.2.1 []).getD p.2.2 0) :=
  let M := first matrixCode (prodCode natCode natCode)
  let ij := second matrixCode (prodCode natCode natCode)
  let i := ij.then (first natCode natCode)
  let j := ij.then (second natCode natCode)
  (j.both ((i.both M).then (getD vectorCode []))).then (getD ratCode 0)

variable {α : Type*}
def Realizes.matrixTabulate {ea : α → Word} {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) :
    Realizes (prodCode (prodCode ea natCode) natCode) matrixCode
      (fun p => (List.range p.1.2).map (fun i => (List.range p.2).map (fun j => f ((p.1.1,i),j)))) :=
  let ec := prodCode ea natCode
  let ctx := first ec natCode
  let a := ctx.then (first ea natCode)
  let cols := ctx.then (second ea natCode)
  let i := second ec natCode
  let row := ((a.both i).both cols).then r.tabulate
  let input := first (prodCode ea natCode) natCode
  let av := input.then (first ea natCode)
  let rows := input.then (second ea natCode)
  let cv := second (prodCode ea natCode) natCode
  ((av.both cv).both rows).then row.tabulate

def identityEntry : Realizes (prodCode natCode natCode) ratCode
    (fun p => if p.1=p.2 then 1 else 0) :=
  (natEq.ite (constant _ ratCode 1) (constant _ ratCode 0)).congr (by intro p;simp)

def identityMatrix : Realizes natCode matrixCode
    (fun n => (List.range n).map (fun i => (List.range n).map (fun j => if i=j then 1 else 0))) :=
  let ctx := prodCode natCode natCode
  let i := (first ctx natCode).then (second natCode natCode)
  let j := second ctx natCode
  let entry := (i.both j).then identityEntry
  (((identity natCode).both (identity natCode)).both (identity natCode)).then entry.matrixTabulate

lemma identityMatrix_data (n : ℕ) :
    (List.range n).map (fun i => (List.range n).map (fun j => if i=j then (1:ℚ) else 0))=
      matrixData (1 : Matrix (Fin n) (Fin n) ℚ) := by
  rw [range_map_fin]
  simp only [range_map_fin,matrixData]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp [Matrix.one_apply,Fin.ext_iff]

def transposeData (M : MatrixData) : MatrixData :=
  (List.range M.length).map (fun i => (List.range M.length).map (fun j => (M.getD j []).getD i 0))

def transposeMatrix : Realizes matrixCode matrixCode transposeData :=
  let ctx := prodCode matrixCode natCode
  let p := first ctx natCode
  let M := p.then (first matrixCode natCode)
  let i := p.then (second matrixCode natCode)
  let j := second ctx natCode
  let entry := (M.both (j.both i)).then matrixEntry
  let n := lengthList vectorCode
  (((identity matrixCode).both n).both n).then entry.matrixTabulate

lemma transpose_data {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    transposeData (matrixData M)=matrixData M.transpose := by
  unfold transposeData matrixData
  simp only [List.length_ofFn,range_map_fin]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [getD_ofFn,getD_ofFn]
  rfl

def matrixMulData (p : MatrixData×MatrixData) : MatrixData :=
  p.1.map (fun row => (transposeData p.2).map (fun col => dotValue (row,col)))

def matrixMul : Realizes (prodCode matrixCode matrixCode) matrixCode matrixMulData :=
  let A := first matrixCode matrixCode
  let Bt := (second matrixCode matrixCode).then transposeMatrix
  let cols := first matrixCode vectorCode
  let row := second matrixCode vectorCode
  let rowResult := (row.both cols).then dot.mapCtx
  (Bt.both A).then rowResult.mapCtx

lemma matrixMul_data {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    matrixMulData (matrixData A,matrixData B)=matrixData (A*B) := by
  unfold matrixMulData
  rw [transpose_data]
  simp only [matrixData,List.map_ofFn,Function.comp_def,dot_ofFn]
  rfl

def fromBlocksData (p : (MatrixData×MatrixData)×(MatrixData×MatrixData)) : MatrixData :=
  zipDefault (fun q : List ℚ×List ℚ => q.1++q.2) [] [] p.1 ++
  zipDefault (fun q : List ℚ×List ℚ => q.1++q.2) [] [] p.2

def fromBlocks : Realizes (prodCode (prodCode matrixCode matrixCode) (prodCode matrixCode matrixCode))
    matrixCode fromBlocksData :=
  let top := (first (prodCode matrixCode matrixCode) (prodCode matrixCode matrixCode)).then
    ((appendList ratCode).zipWith [] [])
  let bot := (second (prodCode matrixCode matrixCode) (prodCode matrixCode matrixCode)).then
    ((appendList ratCode).zipWith [] [])
  (top.both bot).then (appendList vectorCode)

lemma ofFn_sum {n m : ℕ} (f : Fin (n+m) → α) :
    List.ofFn f=List.ofFn (fun i : Fin n => f (finSumFinEquiv (.inl i)))++
      List.ofFn (fun j : Fin m => f (finSumFinEquiv (.inr j))) := by
  exact List.ofFn_add (f := f)

lemma fromBlocks_data {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin m) ℚ) (C : Matrix (Fin m) (Fin n) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ) :
    fromBlocksData ((matrixData A,matrixData B),(matrixData C,matrixData D))=
      matrixData ((Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  unfold fromBlocksData matrixData
  rw [zipDefault_ofFn,zipDefault_ofFn,ofFn_sum]
  congr 1 <;> apply congrArg List.ofFn <;> funext i <;> rw [ofFn_sum] <;>
    simp [Matrix.submatrix]

end CurrentKS.Realization

end OAI
