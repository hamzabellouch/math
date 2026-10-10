import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.ValueDimension
import OAI.Analysis.MatrixSigning.Realization.MatrixStructureRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def natLT : Realizes (prodCode natCode natCode) boolCode (fun p => decide (p.1 < p.2)) :=
  ((((first natCode natCode).then natSucc).both (second natCode natCode)).then natLE).congr
    (by intro p;simp)

def Realizes.scaleMatrix {α : Type*} {ea : α → Word} {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) :
    Realizes ea matrixCode (fun a => (g a).map (fun row => row.map (fun x => f a*x))) :=
  (r.both s).then matrixScale

def negateMatrix : Realizes matrixCode matrixCode
    (fun M => M.map (fun row => row.map (fun x => -x))) :=
  ((constant matrixCode ratCode (-1)).scaleMatrix (identity matrixCode)).congr (by intro M;simp)

def zeroMatrix : Realizes natCode matrixCode (fun n => matrixData (0 : Matrix (Fin n) (Fin n) ℚ)) :=
  ((constant natCode ratCode 0).scaleMatrix identityMatrix).congr (by
    intro n
    rw [identityMatrix_data,matrixScale_data,zero_smul])

def reEntryData (p : (MatrixData×ℕ)×ℕ) : ℚ :=
  if p.1.2 ≤ p.2 then (p.1.1.getD p.1.2 []).getD p.2 0 else (p.1.1.getD p.2 []).getD p.1.2 0

def reEntry : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode reEntryData :=
  let ctx := prodCode matrixCode natCode
  let p := first ctx natCode
  let M := p.then (first matrixCode natCode)
  let i := p.then (second matrixCode natCode)
  let j := second ctx natCode
  let ij := (M.both (i.both j)).then matrixEntry
  let ji := (M.both (j.both i)).then matrixEntry
  (((i.both j).then natLE).ite ij ji).congr (by intro p;simp [reEntryData])

def imEntryData (p : (MatrixData×ℕ)×ℕ) : ℚ :=
  if p.1.2 < p.2 then (p.1.1.getD p.2 []).getD p.1.2 0 else
    if p.2 < p.1.2 then -(p.1.1.getD p.1.2 []).getD p.2 0 else 0

def imEntry : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode imEntryData :=
  let ctx := prodCode matrixCode natCode
  let p := first ctx natCode
  let M := p.then (first matrixCode natCode)
  let i := p.then (second matrixCode natCode)
  let j := second ctx natCode
  let ij := (M.both (i.both j)).then matrixEntry
  let ji := (M.both (j.both i)).then matrixEntry
  (((i.both j).then natLT).ite ji (((j.both i).then natLT).ite ij.neg
    (constant _ ratCode 0))).congr (by intro p;simp [imEntryData])

def squareTabData (f : (MatrixData×ℕ)×ℕ → ℚ) (p : ℕ×MatrixData) : MatrixData :=
  (List.range p.1).map (fun i => (List.range p.1).map (fun j => f ((p.2,i),j)))

def squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) :
    Realizes (prodCode natCode matrixCode) matrixCode (squareTabData f) :=
  let n := first natCode matrixCode
  let M := second natCode matrixCode
  ((M.both n).both n).then r.matrixTabulate

def realDecodeData (p : ℕ×MatrixData) : MatrixData :=
  let re := squareTabData reEntryData p
  let im := squareTabData imEntryData p
  fromBlocksData ((re,im.map (fun row => row.map (fun x => -x))),(im,re))

def realDecode : Realizes (prodCode natCode matrixCode) matrixCode realDecodeData :=
  let re := squareTabulate reEntry
  let im := squareTabulate imEntry
  ((re.both (im.then negateMatrix)).both (im.both re)).then fromBlocks

lemma reEntry_data {d : ℕ} (x : Fin d×Fin d → ℚ) (i j : Fin d) :
    reEntryData ((matrixData (fun i j => x (i,j)),i.val),j.val)=x (min i j,max i j) := by
  unfold reEntryData matrixData
  rw [getD_ofFn,getD_ofFn,getD_ofFn,getD_ofFn]
  by_cases h : i ≤ j
  · simp [h,show i.val ≤ j.val from h]
  · have h' : j ≤ i := le_of_not_ge h
    simp [min_eq_right h',max_eq_left h',show ¬i.val ≤ j.val from h]

lemma imEntry_data {d : ℕ} (x : Fin d×Fin d → ℚ) (i j : Fin d) :
    imEntryData ((matrixData (fun i j => x (i,j)),i.val),j.val)=
      (if i < j then x (j,i) else if j < i then -x (i,j) else 0) := by
  unfold imEntryData matrixData
  rw [getD_ofFn,getD_ofFn,getD_ofFn,getD_ofFn]
  rfl

lemma squareTab_data {d : ℕ} (f : (MatrixData×ℕ)×ℕ → ℚ) (x : Fin d×Fin d → ℚ) :
    squareTabData f (d,matrixData (fun i j => x (i,j)))=
      matrixData (fun i j : Fin d => f ((matrixData (fun i j => x (i,j)),i.val),j.val)) := by
  simp only [squareTabData,range_map_fin,matrixData]

lemma realDecode_data {d : ℕ} (x : Fin d×Fin d → ℚ) :
    realDecodeData (d,matrixData (fun i j => x (i,j)))=matrixData (RationalSDP.realFinDecode d x) := by
  simp only [realDecodeData,squareTab_data,reEntry_data,imEntry_data]
  have hn (M : Matrix (Fin d) (Fin d) ℚ) :
      (matrixData M).map (fun row => row.map (fun x => -x))=matrixData (-M) := by
    simp only [matrixData,List.map_ofFn,Function.comp_def];rfl
  erw [hn,fromBlocks_data]
  rfl

end CurrentKS.Realization

end OAI
