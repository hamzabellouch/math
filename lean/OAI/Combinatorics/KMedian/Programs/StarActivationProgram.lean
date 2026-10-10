import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseStarActivation
import OAI.Combinatorics.KMedian.Programs.GraphRunProgram
import OAI.Combinatorics.KMedian.Rounding.TargetSubsetProgram

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  q : Fin m → ℚ
  feasible : ∀ e, 0≤q e ∧ q e≤1
abbrev Raw := List Unit × (Table × List ℚ)
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),List.ofFn x.q))
abbrev Input.encode (x : Input) := enc x.raw

def Input.column (x : Input) (e : Fin x.m) : SparseTargetSubset.Program.Input :=
  ⟨x.n,x.D e,x.q e,x.feasible e⟩
def Input.columns (x : Input) := List.ofFn x.column

def prepare (x : Raw) : List SparseTargetSubset.Program.Raw :=
  (indices x.2.2).map (fun e => (x.2.1[e]?.getD [],x.2.2[e]?.getD 0))
@[fun_prop] theorem prepare_poly : Poly prepare := by unfold prepare; apply list_map <;> fun_prop
 theorem prepare_input (x : Input) : prepare x.raw=x.columns.map SparseTargetSubset.Program.Input.raw := by
  simp only [prepare,Input.raw,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,Input.columns]
  rfl
noncomputable def columnsProgram : PolyProgram Input.encode (encodeList SparseTargetSubset.Program.Input.encode) Input.columns :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    change encodeList enc (prepare x.raw)=_
    rw [prepare_input,RoundingProgram.encodeList_map])

def dummy : SparseTargetSubset.Program.Input := ⟨0,∅,0,by norm_num⟩
def Input.graph (x : Input) : SparseGraph.Program.Input :=
  ⟨x.n,x.m,fun e => SparseTargetSubset.law (x.D e) (x.q e)⟩
noncomputable def graphProgram : PolyProgram Input.encode SparseGraph.Program.Input.encode Input.graph := by
  let n : PolyProgram Input.encode enc (fun x : Input => x.raw.1) :=
    (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let columns := columnsProgram.comp (SparseTargetSubset.Program.program.listMap dummy)
  exact (n.fanout columns).recode id (fun _ => rfl) (fun x => by
    change SparseGraph.Program.ei (x.raw.1,x.columns.map SparseTargetSubset.Program.Input.result)=_
    simp only [Input.columns,List.map_ofFn,Function.comp_def]
    rfl)

def Input.result (x : Input) : Data Table :=
  (((law x.D x.q).law.denominator,List.ofFn (law x.D x.q).law.numerator),
    (law x.D x.q).states.toList.map SparseGraph.ListOperation.view)
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et) Input.result := by
  let get : PolyProgram SparseGraph.Program.State.encode (ed SparseGraph.ListOperation.et)
      (fun x : SparseGraph.Program.State => (x.raw SparseGraph.Program.view).2) :=
    (snd SparseGraph.Program.Context.encode (ed SparseGraph.ListOperation.et)).recode
      (SparseIntegerLaw.DependentProgram.Bundle.raw SparseGraph.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (graphProgram.comp SparseGraph.Program.runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseStarActivation.Program
end

end OAI
