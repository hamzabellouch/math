import Mathlib
import OAI.Analysis.MatrixSigning.Realization.PencilArrayRealization
import OAI.Analysis.MatrixSigning.Realization.CoordinateRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

abbrev ValueData := ℕ×(List MatrixData×(List ℚ×(List ℚ×ℚ)))
abbrev valueDataCode := prodCode natCode (prodCode (listCode matrixCode)
  (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdD := first natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdRest := Realization.second natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdAtoms := vdRest.then (first (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdParams := vdRest.then (second (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdX := vdParams.then (first vectorCode (prodCode vectorCode ratCode))
def vdTheta := vdParams.then ((second vectorCode (prodCode vectorCode ratCode)).then (first vectorCode ratCode))
def vdEps := vdParams.then ((second vectorCode (prodCode vectorCode ratCode)).then (second vectorCode ratCode))
def realDimension : Realizes natCode natCode (fun d => d+d) :=
  ((identity natCode).both (identity natCode)).then natAdd
def valueDimension : Realizes natCode natCode RationalSDP.valueDimension :=
  let sq := ((identity natCode).both (identity natCode)).then natMul
  (((sq.both sq).then natAdd).then natSucc).congr (by intro d;simp [RationalSDP.valueDimension,Nat.add_comm])

def valueData {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) : ValueData :=
  (d,(List.ofFn (fun i => matrixData (RationalSDP.realFinDecode d (coords i))),
    (List.ofFn x,(List.ofFn θ,ε))))

abbrev matrixVarCode := prodCode natCode vectorCode

def coordinateIndex (second : Bool) (p : (ℕ×ℕ)×ℕ) : ℕ :=
  1+(if second then p.1.1*p.1.1 else 0)+(p.2+p.1.1*p.1.2)
def coordinateIndexRealizes (second : Bool) :
    Realizes (prodCode (prodCode natCode natCode) natCode) natCode (coordinateIndex second) :=
  let p := first (prodCode natCode natCode) natCode
  let d := p.then (first natCode natCode)
  let i := p.then (Realization.second natCode natCode)
  let j := Realization.second (prodCode natCode natCode) natCode
  let offset := (constant _ boolCode second).ite ((d.both d).then natMul) (constant _ natCode 0)
  let start := ((constant _ natCode 1).both offset).then natAdd
  let row := (d.both i).then natMul
  (start.both ((j.both row).then natAdd)).then natAdd

lemma coordinateIndex_value {d : ℕ} (second : Bool) (i j : Fin d) :
    coordinateIndex second ((d,i.val),j.val)=
      (RationalSDP.valueIndex d (.inr (if second then .inr (i,j) else .inl (i,j)))).val := by
  cases second
  · change 1+0+(j.val+d*i.val)=1+(j.val+d*i.val)
    omega
  · change 1+d*d+(j.val+d*i.val)=1+(d*d+(j.val+d*i.val))
    omega

def coordinateEntry (second : Bool) :
    Realizes (prodCode (prodCode matrixVarCode natCode) natCode) ratCode
      (fun p => p.1.1.2.getD (coordinateIndex second ((p.1.1.1,p.1.2),p.2)) 0) :=
  let ctx := first (prodCode matrixVarCode natCode) natCode
  let data := ctx.then (first matrixVarCode natCode)
  let d := data.then (first natCode vectorCode)
  let y := data.then (Realization.second natCode vectorCode)
  let i := ctx.then (Realization.second matrixVarCode natCode)
  let j := Realization.second (prodCode matrixVarCode natCode) natCode
  let idx := ((d.both i).both j).then (coordinateIndexRealizes second)
  (idx.both y).then (getD ratCode 0)

def coordinateData (second : Bool) (p : ℕ×List ℚ) : MatrixData :=
  (List.range p.1).map (fun i => (List.range p.1).map
    (fun j => p.2.getD (coordinateIndex second ((p.1,i),j)) 0))
def coordinates (second : Bool) : Realizes matrixVarCode matrixCode (coordinateData second) :=
  let d := first natCode vectorCode
  (((identity matrixVarCode).both d).both d).then (coordinateEntry second).matrixTabulate

def matrixVariableData (second : Bool) (p : ℕ×List ℚ) :=
  realDecodeData (p.1,coordinateData second p)
def matrixVariable (second : Bool) : Realizes matrixVarCode matrixCode (matrixVariableData second) :=
  ((first natCode vectorCode).both (coordinates second)).then realDecode

lemma coordinates_data {d : ℕ} (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    coordinateData second (d,List.ofFn y)=
      matrixData (fun i j => RationalSDP.matrixCoordinate d second y (i,j)) := by
  unfold coordinateData
  simp only [range_map_fin,matrixData]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [coordinateIndex_value,getD_ofFn]
  rfl
lemma matrixVariable_data {d : ℕ} (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    matrixVariableData second (d,List.ofFn y)=matrixData (RationalSDP.matrixVariable d second y) := by
  rw [matrixVariableData,coordinates_data,realDecode_data]
  rfl

def weightedSumData (p : ℕ×(List ℚ×List MatrixData)) : MatrixData :=
  (zipDefault (id : ℚ×MatrixData → ℚ×MatrixData) 0 [] p.2).foldl
    (fun a b => accumMatrix (a,b)) (matrixData (0 : Matrix (Fin p.1) (Fin p.1) ℚ))
def weightedSum : Realizes (prodCode natCode (prodCode vectorCode (listCode matrixCode))) matrixCode weightedSumData :=
  let n := first natCode (prodCode vectorCode (listCode matrixCode))
  let values := Realization.second natCode (prodCode vectorCode (listCode matrixCode))
  let pairs := values.then ((identity (prodCode ratCode matrixCode)).zipWith 0 [])
  ((n.then zeroMatrix).both pairs).then accumMatrixRealizes.fold
lemma weightedSum_data {n N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℚ) (x : Fin N → ℚ) :
    weightedSumData (n,(List.ofFn x,List.ofFn (fun i => matrixData (A i))))=
      matrixData (∑ i,x i • A i) := by
  unfold weightedSumData
  rw [zipDefault_ofFn]
  have he : List.ofFn (fun i => (x i,matrixData (A i)))=
      (List.ofFn (fun i => (x i,A i))).map (fun p => (p.1,matrixData p.2)) := by
    simp only [List.map_ofFn,Function.comp_def]
  change (List.ofFn (fun i => (x i,matrixData (A i)))).foldl _ _=_
  rw [he,fold_matrixData]
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,zero_add]

def sandwichData (p : MatrixData×MatrixData) : MatrixData :=
  matrixMulData (matrixMulData (p.1,p.2),p.1)
def sandwich : Realizes (prodCode matrixCode matrixCode) matrixCode sandwichData :=
  (matrixMul.both (first matrixCode matrixCode)).then matrixMul
lemma sandwich_data {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℚ) :
    sandwichData (matrixData A,matrixData Z)=matrixData (A*Z*A) := by
  rw [sandwichData,matrixMul_data,matrixMul_data]

end CurrentKS.Realization

end

end OAI
