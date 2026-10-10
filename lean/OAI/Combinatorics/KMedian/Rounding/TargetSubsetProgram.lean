import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseTargetSubset
import OAI.Combinatorics.KMedian.Programs.CardinalRoundProgram
import OAI.Combinatorics.KMedian.Programs.LastFractionProgram

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
structure Input where
  n : ℕ
  D : Finset (Fin n)
  q : ℚ
  feasible : 0≤q ∧ q≤1
abbrev Raw := Row × ℚ
def Input.raw (x : Input) : Raw := (setView x.D,x.q)
abbrev Input.encode (x : Input) := enc x.raw

def Input.weighted (x : Input) : RoundingProgram.Input false :=
  ⟨x.n,fun _ => 1,initial x.D x.q,fun _ _ => by norm_num,initial_unit x.D x.feasible⟩
def prepare (x : Raw) : List ℚ × List ℚ := (x.1.map (fun _ => 1),x.1.map (fun b => if b then x.2 else 0))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply pair <;> apply list_map <;> fun_prop
 theorem prepare_input (x : Input) : prepare x.raw=x.weighted.raw := by
  simp only [prepare,Input.raw,setView,List.map_ofFn,Function.comp_def,Input.weighted,RoundingProgram.Input.raw,
    initial,Vector.toList_ofFn,decide_eq_true_eq]

def Input.result (x : Input) := SparseGraph.Program.columnRaw (law x.D x.q)
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.er) Input.result := by
  let p : PolyProgram Input.encode RoundingProgram.Input.encode Input.weighted :=
    prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input x))
  let get : PolyProgram RoundingProgram.State.encode (ed RoundingProgram.erow)
      (fun x : RoundingProgram.State false => RoundingProgram.vectorData x.μ) :=
    (snd RoundingProgram.erow (ed RoundingProgram.erow)).recode RoundingProgram.State.raw
      RoundingProgram.State.encode_raw (fun _ => rfl)
  let post : PolyProgram (ed RoundingProgram.erow) (ed SparseGraph.ListOperation.er)
      (fun x : Data (List ℚ) => (x.1,x.2.map SparseCardinalRounding.Program.selectedRow)) := by
    apply Poly.program
    apply pair
    · fun_prop
    · apply list_map <;> fun_prop
  exact (p.comp RoundingProgram.WeightedRound.program |>.comp get |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,Input.result,law,SparseGraph.Program.columnRaw,SparseIntegerLaw.map,RoundingProgram.vectorData,
      Vector.toList_map,List.map_map,SparseCardinalRounding.Program.selectedRow_eq]
    rfl)
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
