import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Lookup
import OAI.Analysis.MatrixSigning.Realization.MatrixStructureRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

abbrev indicesCode := listCode natCode

def activeData (xs : List ℚ) : List ℕ :=
  (List.range xs.length).filter (fun j => decide (|xs.getD j 0| < 1))
def activeIndices : Realizes vectorCode indicesCode activeData :=
  let xs := first vectorCode natCode
  let j := second vectorCode natCode
  let value := (j.both xs).then (getD ratCode 0)
  let test := value.abs.lt (constant (prodCode vectorCode natCode) ratCode 1)
  (((identity vectorCode).both ((lengthList ratCode).then range)).then test.filterCtx)

lemma range_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by simp
lemma activeData_data {N : ℕ} (x : Fin N → ℚ) :
    activeData (List.ofFn x)=(RationalFace.activeIndices x).map Fin.val := by
  unfold activeData RationalFace.activeIndices
  rw [List.length_ofFn,range_finRange,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [Function.comp_apply,getD_ofFn]

abbrev extendDataCode := prodCode indicesCode (prodCode vectorCode vectorCode)
def extendEntryData (p : (List ℕ×(List ℚ×List ℚ))×ℕ) : ℚ :=
  ((List.range p.1.1.length).find? (fun j => p.1.1.getD j 0==p.2)).elim
    (p.1.2.1.getD p.2 0) (fun j => p.1.2.2.getD j 0)

def extendEntry : Realizes (prodCode extendDataCode natCode) ratCode extendEntryData :=
  let pc := prodCode extendDataCode natCode
  let data := first extendDataCode natCode
  let e := data.then (first indicesCode (prodCode vectorCode vectorCode))
  let vecs := data.then (second indicesCode (prodCode vectorCode vectorCode))
  let base := vecs.then (first vectorCode vectorCode)
  let y := vecs.then (second vectorCode vectorCode)
  let i := second extendDataCode natCode
  let fallback := (i.both base).then (getD ratCode 0)
  let ctx := first pc natCode
  let j := second pc natCode
  let test := ((((j.both (ctx.then e)).then (getD natCode 0)).both (ctx.then i)).then natEq)
  let val := (j.both (ctx.then y)).then (getD ratCode 0)
  (((identity pc).both (fallback.both ((e.then (lengthList natCode)).then range))).then
    (test.findValue val)).congr (by intro p;simp only [extendEntryData,beq_eq_decide,id_eq])

def extendData (p : List ℕ×(List ℚ×List ℚ)) : List ℚ :=
  (List.range p.2.1.length).map (fun i => extendEntryData (p,i))
def extendVector : Realizes extendDataCode vectorCode extendData :=
  let base := (second indicesCode (prodCode vectorCode vectorCode)).then (first vectorCode vectorCode)
  (((identity extendDataCode).both (base.then (lengthList ratCode))).then extendEntry.tabulate)

lemma extendEntry_data {N n : ℕ} (e : Fin n → Fin N) (base : Fin N → ℚ) (y : Fin n → ℚ) (i : Fin N) :
    extendEntryData ((List.ofFn (fun j => (e j).val),(List.ofFn base,List.ofFn y)),i.val)=
      RationalFace.extend e base y i := by
  unfold extendEntryData RationalFace.extend RationalFace.lookup
  rw [List.length_ofFn,range_finRange,List.find?_map,getD_ofFn]
  have hp : (fun j : Fin n => (List.ofFn fun j => (e j).val).getD j.val 0==i.val)=
      fun j => e j==i := by
    funext j
    rw [getD_ofFn]
    simp [Fin.ext_iff]
  change (((List.finRange n).find? (fun j : Fin n => (List.ofFn fun j => (e j).val).getD j.val 0==i.val)).map Fin.val).elim (base i) (fun j => (List.ofFn y).getD j 0)=_
  rw [hp]
  cases hh : (List.finRange n).find? (fun j => e j==i) with
  | none => rfl
  | some j => simp

lemma extendData_data {N n : ℕ} (e : Fin n → Fin N) (base : Fin N → ℚ) (y : Fin n → ℚ) :
    extendData (List.ofFn (fun j => (e j).val),(List.ofFn base,List.ofFn y))=
      List.ofFn (RationalFace.extend e base y) := by
  unfold extendData
  rw [List.length_ofFn,range_map_fin]
  apply congrArg List.ofFn
  funext i
  exact extendEntry_data e base y i

lemma activeIndex_data {N : ℕ} (x : Fin N → ℚ) :
    activeData (List.ofFn x)=List.ofFn (fun j => (RationalFace.activeIndex x j).val) := by
  rw [activeData_data]
  symm
  change List.ofFn (Fin.val ∘ (RationalFace.activeIndices x).get)=_
  rw [←List.map_ofFn,List.ofFn_get]

end CurrentKS.Realization

end OAI
