import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedRounding
import OAI.Combinatorics.KMedian.Sparse.SparseTable
import OAI.Combinatorics.KMedian.Rounding.SignedTerminalProgram

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

def emptyInput : Input true := ⟨0,Fin.elim0,#v[],by simp,fun i => Fin.elim0 i⟩
def partialInput (x : Input true) (i : Fin (SparseSignedPartial.run x.β x.p x.n).length) : Input true :=
  ⟨x.n,x.β,(SparseSignedPartial.run x.β x.p x.n).states[i.val],x.positive,
    (SparseSignedPartial.run_invariants _ _ x.feasible _ i).1⟩
def partialInputs (x : Input true) : List (Input true) := List.ofFn (partialInput x)
def boundState (x : Input true) : State true :=
  ⟨x.n,x.β,x.positive,(SparseSignedPartial.run x.β x.p x.n).bindIndexed (SparseSignedRounding.kernel x.β x.p x.feasible)⟩
def result (x : Input true) : State true :=
  ⟨x.n,x.β,x.positive,SparseSignedRounding.round x.β x.p x.feasible⟩

noncomputable def partialInputsProgram : PolyProgram Input.encode (encodeList Input.encode) partialInputs := by
  let inputctx := (fst erow erow).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  let part :=  runProgram true
  let rows := part.comp (statesProgram true)
  let raw := (inputctx.fanout rows).comp ((PolyProgram.identity (encodePair erow erow)).listMapWith [] ([],[]))
  exact raw.recode id (fun _ => rfl) (fun x => by
    change encodeList (encodePair erow erow)
      (((x.run x.n).μ.states.toList.map Vector.toList).map (fun p => (List.ofFn x.β,p)))=_
    simp only [states_list,List.map_ofFn,Function.comp_def]
    change encodeList (encodePair erow erow) (List.ofFn fun i =>
      (Input.raw (partialInput x i)))=encodeList Input.encode (List.ofFn (partialInput x))
    rw [List.ofFn_comp',encodeList_map])

noncomputable def boundProgram : PolyProgram Input.encode State.encode boundState := by
  let part :=  runProgram true
  let law := part.comp ((snd erow (ed erow)).comp (fst el (encodeList erow)) |>.recode (@State.raw true) State.encode_raw (fun _ => rfl))
  let kernels := partialInputsProgram.comp (Terminal.program.listMap emptyInput)
  let bound := (law.fanout kernels).comp SparseIntegerLaw.BinarySparse.bindData_poly.program
  let β := (fst erow erow).recode (@Input.raw true) (fun _ => rfl) (fun _ => rfl)
  exact (β.fanout bound).recode id (fun _ => rfl) (fun x => by
    rw [← State.encode_raw]
    change encodePair erow (ed erow) (List.ofFn x.β,
      bindData (((SparseSignedPartial.run x.β x.p x.n).law.denominator,
        List.ofFn (SparseSignedPartial.run x.β x.p x.n).law.numerator),
        (partialInputs x).map Terminal.result))=_
    simp only [partialInputs,List.map_ofFn,Function.comp_def]
    change encodePair erow (ed erow) (List.ofFn x.β,
      bindData ((raw (SparseSignedPartial.run x.β x.p x.n)).1,
        List.ofFn (fun i => ((raw (SparseSignedRounding.kernel x.β x.p x.feasible i)).1,
          (SparseSignedRounding.kernel x.β x.p x.feasible i).states.toList.map Vector.toList))))=_
    rw [bindData_raw]
    rfl)

noncomputable def program : PolyProgram Input.encode State.encode result :=
  (boundProgram.comp (compressProgram true)).congr _ (fun _ => rfl)

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
