import Mathlib
import OAI.Combinatorics.KMedian.Geometry.TrimIntegerLaw
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Geometry.SortedListEncoding
import OAI.Combinatorics.KMedian.Programs.PivotListProgram

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
abbrev LawData := IntegerLaw.ListPivot.LawData
abbrev el := IntegerLaw.ListPivot.el
abbrev er := IntegerLaw.ListPivot.er
variable {α : Type}
abbrev Data (α : Type) := LawData × List α
abbrev ed (ea : α → List Bool) := encodePair el (encodeList ea)

def raw (μ : SparseIntegerLaw α) : Data α :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList)
abbrev encode (ea : α → List Bool) (μ : SparseIntegerLaw α) := ed ea (raw μ)

def activeEntries (x : Data α) : List (ℤ × α) :=
  (x.1.2.zip x.2).filter (fun z => decide (z.1≠0))
def trimData (x : Data α) : Data α :=
  ((x.1.1,(activeEntries x).map Prod.fst),(activeEntries x).map Prod.snd)

theorem states_list (μ : SparseIntegerLaw α) : μ.states.toList=List.ofFn (fun i : Fin μ.length => μ.states[i.val]) := by
  apply List.ext_getElem <;> intros <;> simp

theorem activeEntries_raw (μ : SparseIntegerLaw α) : activeEntries (raw μ)=
    List.ofFn (fun j : Fin μ.law.support.card => let i := μ.law.support.orderEmbOfFin rfl j;
      (μ.law.numerator i,μ.states[i.val])) := by
  rw [activeEntries,raw,states_list,Gaussian.ListOperation.zip_ofFn,List.ofFn_eq_map,List.filter_map]
  exact EncodingLists.map_filter_enum _ (fun i => μ.law.numerator i≠0)

theorem trimData_raw (μ : SparseIntegerLaw α) : trimData (raw μ)=raw μ.trim := by
  unfold trimData
  rw [activeEntries_raw]
  simp only [raw,trim,Vector.toList_ofFn,List.map_ofFn,Function.comp_def,IntegerLaw.trim_denominator]
  congr 2
  exact congrArg List.ofFn (funext (IntegerLaw.trim_numerator μ.law)).symm

noncomputable def activeProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (ed ea) (encodeList (encodePair Signed.encode ea)) activeEntries := by
  let l := fst el (encodeList ea)
  let nums := l.comp (snd Signed.encode er)
  let s := snd el (encodeList ea)
  let test := ((((fst Signed.encode ea).fanout (constant (encodePair Signed.encode ea) Signed.encode 0)).comp intEQ).comp boolNot)
  exact (((nums.fanout s).comp (listZip Signed.encode ea 0 a0)).comp (test.listFilter (0,a0))).congr _ (fun x => by
    simp only [Function.comp_def,activeEntries,decide_not])

noncomputable def trimDataProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (ed ea) (ed ea) trimData := by
  let zs := activeProgram ea a0
  let nums := zs.comp ((fst Signed.encode ea).listMap (0,a0))
  let states := zs.comp ((snd Signed.encode ea).listMap (0,a0))
  let den := (fst el (encodeList ea)).comp (fst Signed.encode er)
  exact ((den.fanout nums).fanout states).congr _ (fun _ => rfl)

noncomputable def trimProgram (ea : α → List Bool) (a0 : α) :
    PolyProgram (encode ea) (encode ea) (SparseIntegerLaw.trim (α:=α)) :=
  (trimDataProgram ea a0).recode raw (fun _ => rfl) (fun μ => by rw [trimData_raw])
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
