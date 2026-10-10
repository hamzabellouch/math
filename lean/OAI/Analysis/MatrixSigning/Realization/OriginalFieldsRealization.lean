import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Coordinates
import OAI.Analysis.MatrixSigning.Realization.DependentRealization
import OAI.Analysis.MatrixSigning.Encoding.FlattenLookup
import OAI.Analysis.MatrixSigning.Realization.DenseInputArrays

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def fieldValues (x : Input) (i : Fin x.N) : List ℚ :=
  (DenseInputArrays.fields x i).map RationalEntry.value
lemma fieldValues_eq (x : Input) (i : Fin x.N) :
    fieldValues x i=(List.ofFn fun j : Fin x.d =>
      (List.ofFn fun k : Fin x.d => [(x.entries i j k).1.value,(x.entries i j k).2.value]).flatten).flatten := by
  simp [fieldValues,DenseInputArrays.fields,List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def]

lemma fieldValues_get (x : Input) (i : Fin x.N) (j k : Fin x.d) (b : Fin 2) :
    (fieldValues x i).getD (2*(j.val*x.d+k.val)+b.val) 0=
      (if b.val=0 then (x.entries i j k).1.value else (x.entries i j k).2.value) := by
  rw [fieldValues_eq]
  have hl (j : Fin x.d) :
      ((List.ofFn fun k : Fin x.d => [(x.entries i j k).1.value,(x.entries i j k).2.value]).flatten).length=2*x.d := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_cons,List.length_nil]
    simp
    omega
  have he : 2*(j.val*x.d+k.val)+b.val=j.val*(2*x.d)+(k.val*2+b.val) := by ring
  rw [he,getD_flatten_ofFn _ hl j _ (by have hk := k.isLt;have hb := b.isLt;omega)]
  rw [getD_flatten_ofFn (fun k : Fin x.d => [(x.entries i j k).1.value,(x.entries i j k).2.value]) (m := 2) (fun _ => rfl) k b.val b.isLt]
  fin_cases b <;> simp

abbrev originalDataCode := prodCode natCode (listCode vectorCode)
def originalData (x : Input) := (x.d,List.ofFn (fieldValues x))
def originalCode (x : Input) : Word := originalDataCode (originalData x)
def originalView : Realizes originalCode originalDataCode originalData :=
  (identity originalDataCode).reindex originalCode originalData (fun _ => rfl)
def originalD : Realizes originalCode natCode Input.d := originalView.then (first natCode (listCode vectorCode))
def originalRecords : Realizes originalCode (listCode vectorCode) (fun x => List.ofFn (fieldValues x)) :=
  originalView.then (second natCode (listCode vectorCode))
def originalN : Realizes originalCode natCode Input.N :=
  (originalRecords.then (lengthList vectorCode)).congr (fun _ => List.length_ofFn)

abbrev recordCode := prodCode natCode vectorCode
abbrev recordPointCode := prodCode (prodCode recordCode natCode) natCode

def recordEntryData (imag : Bool) (p : ((ℕ×List ℚ)×ℕ)×ℕ) : ℚ :=
  p.1.1.2.getD (2*(p.1.2*p.1.1.1+p.2)+(if imag then 1 else 0)) 0

def recordEntry (imag : Bool) : Realizes recordPointCode ratCode (recordEntryData imag) :=
  let r := (first (prodCode recordCode natCode) natCode).then (first recordCode natCode)
  let d := r.then (first natCode vectorCode)
  let fields := r.then (second natCode vectorCode)
  let i := (first (prodCode recordCode natCode) natCode).then (second recordCode natCode)
  let j := second (prodCode recordCode natCode) natCode
  let offset := (((i.both d).then natMul).both j).then natAdd
  let twice := ((constant recordPointCode natCode 2).both offset).then natMul
  (((twice.both (constant recordPointCode natCode (if imag then 1 else 0))).then natAdd).both fields).then (getD ratCode 0)

def recordCoordinateData (p : ((ℕ×List ℚ)×ℕ)×ℕ) : ℚ :=
  if p.1.2≤p.2 then recordEntryData false p else recordEntryData true ((p.1.1,p.2),p.1.2)
def recordCoordinate : Realizes recordPointCode ratCode recordCoordinateData :=
  let r := (first (prodCode recordCode natCode) natCode).then (first recordCode natCode)
  let i := (first (prodCode recordCode natCode) natCode).then (second recordCode natCode)
  let j := second (prodCode recordCode natCode) natCode
  (((i.both j).then natLE).ite (recordEntry false) (((r.both j).both i).then (recordEntry true))).congr
    (by intro p;simp only [recordCoordinateData,decide_eq_true_eq])

def recordCoordinatesData (p : ℕ×List ℚ) : MatrixData :=
  (List.range p.1).map (fun i => (List.range p.1).map (fun j => recordCoordinateData ((p,i),j)))
def recordCoordinates : Realizes recordCode matrixCode recordCoordinatesData :=
  let d := first natCode vectorCode
  (((identity recordCode).both d).both d).then recordCoordinate.matrixTabulate
lemma recordCoordinate_data (x : Input) (i : Fin x.N) (j k : Fin x.d) :
    recordCoordinateData (((x.d,fieldValues x i),j.val),k.val)=RationalInput.coordinates x i (j,k) := by
  unfold recordCoordinateData RationalInput.coordinates
  change (if j.val≤k.val then _ else _)=
    (if j.val≤k.val then (x.entries i j k).1.value else (x.entries i k j).2.value)
  by_cases hle : j.val≤k.val
  · simp only [hle,ite_true,recordEntryData,Bool.false_eq_true,ite_false,Nat.add_zero]
    have hh := fieldValues_get x i j k (0 : Fin 2)
    simpa using hh
  · simp only [hle,ite_false,recordEntryData,ite_true]
    have hh := fieldValues_get x i k j (1 : Fin 2)
    simpa using hh
lemma recordCoordinates_data (x : Input) (i : Fin x.N) :
    recordCoordinatesData (x.d,fieldValues x i)=matrixData (fun j k => RationalInput.coordinates x i (j,k)) := by
  simp only [recordCoordinatesData,range_map_fin,matrixData,recordCoordinate_data]

def originalRecord : Realizes (finFamilyCode originalCode Input.N) recordCode
    (fun p => (p.1.d,fieldValues p.1 p.2)) :=
  let x : Realizes (finFamilyCode originalCode Input.N) originalCode (fun p => p.1) := familyFirst
  let i : Realizes (finFamilyCode originalCode Input.N) natCode (fun p => p.2.val) := familyIndex
  ((x.then originalD).both ((i.both (x.then originalRecords)).then (getD vectorCode []))).congr
    (by intro p;rw [getD_ofFn])

def originalCoordinates : Realizes originalCode (listCode matrixCode)
    (fun x => List.ofFn (fun i => matrixData (fun j k => RationalInput.coordinates x i (j,k)))) :=
  ((originalRecord.then recordCoordinates).tabulateFin originalN).congr
    (by intro x;apply congrArg List.ofFn;funext i;exact recordCoordinates_data x i)

end CurrentKS.Realization

end

end OAI
