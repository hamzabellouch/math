import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliStepProgram
import OAI.Combinatorics.KMedian.Programs.GraphStepProgram
import OAI.Combinatorics.KMedian.Process.RoundingRunProgram

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
abbrev Input := SparseBernoulli.Program.Input
abbrev encodeInput := SparseBernoulli.Program.Input.encode
abbrev qr := encodeList Ratio.encode
abbrev br := encodeList encodeBool

def weightedInput (x : Input) : RoundingProgram.Input false :=
  ⟨x.n,fun _ => 1,Vector.ofFn x.p,fun _ _ => by norm_num,fun i => by
    simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using x.feasible i⟩
def result (x : Input) : Data (List Bool) :=
  SparseGraph.Program.columnRaw ((round (Vector.ofFn x.p)).map selected)

noncomputable def inputProgram : PolyProgram encodeInput RoundingProgram.Input.encode weightedInput := by
  have hm : Binary.Automatic.Poly (fun q : List ℚ => q.map (fun _ => (1:ℚ))) := by
    apply Binary.Automatic.Poly.list_map <;> fun_prop
  let p : PolyProgram qr (encodePair qr qr) (fun q : List ℚ => (q.map (fun _ => (1:ℚ)),q)) :=
    Binary.Automatic.Poly.program (by fun_prop)
  exact p.recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by
    simp only [List.map_const',List.length_ofFn,RoundingProgram.Input.encode,
      RoundingProgram.Input.raw,weightedInput,List.ofFn_const,Vector.toList_ofFn])

def selectedRow (p : List ℚ) : List Bool := p.map (fun q => decide (q=1))
@[fun_prop] theorem selectedRow_poly : Binary.Automatic.Poly selectedRow := by
  unfold selectedRow
  apply Binary.Automatic.Poly.list_map <;> fun_prop
 theorem selectedRow_eq {n : ℕ} (q : Vector ℚ n) :
    selectedRow q.toList=SparseGraph.ListOperation.setView (selected q) := by
  apply List.ext_getElem
  · simp only [selectedRow,List.length_map,Vector.length_toList,SparseGraph.ListOperation.setView,List.length_ofFn]
  · intro i hi hi'
    have hin : i<n := by simpa only [SparseGraph.ListOperation.setView,List.length_ofFn] using hi'
    simp only [selectedRow,List.getElem_map,Vector.getElem_toList,SparseGraph.ListOperation.setView,
      List.getElem_ofFn,selected,Finset.mem_filter,Finset.mem_univ,true_and,RationalWeightedStep.point]

noncomputable def program : PolyProgram encodeInput (ed br) result := by
  let part := inputProgram.comp (RoundingProgram.runProgram false)
  let get : PolyProgram RoundingProgram.State.encode (ed RoundingProgram.erow)
      (fun x : RoundingProgram.State false => RoundingProgram.vectorData x.μ) :=
    (snd RoundingProgram.erow (ed RoundingProgram.erow)).recode RoundingProgram.State.raw
      RoundingProgram.State.encode_raw (fun _ => rfl)
  let post : PolyProgram (ed RoundingProgram.erow) (ed br)
      (fun x : Data (List ℚ) => (x.1,x.2.map selectedRow)) := by
    apply Binary.Automatic.Poly.program
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact (part.comp get |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,result,RoundingProgram.vectorData,SparseGraph.Program.columnRaw,
      SparseIntegerLaw.map,Vector.toList_map,List.map_map,selectedRow_eq]
    rfl)
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
