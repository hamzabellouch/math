import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseGridRounding
import OAI.Combinatorics.KMedian.Programs.CardinalRoundProgram
import OAI.Combinatorics.KMedian.Binary.BinaryFloor

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
structure Input where
  n : ℕ
  q : Fin n → ℚ
  nonnegative : ∀ i, 0≤q i
abbrev Input.raw (x : Input) := List.ofFn x.q
abbrev Input.encode (x : Input) := enc x.raw

def fractionRow (q : List ℚ) : List ℚ := q.map (fun x => x-(⌊x⌋₊:ℚ))
@[fun_prop] theorem fractionRow_poly : Poly fractionRow := by unfold fractionRow; apply list_map <;> fun_prop
 theorem fractionRow_list {n : ℕ} (q : Fin n → ℚ) : fractionRow (List.ofFn q)=(fraction q).toList := by
  simp only [fractionRow,List.map_ofFn,fraction,base,Function.comp_def,Vector.toList_ofFn]
def Input.cardinal (x : Input) : SparseCardinalRounding.Program.Input :=
  ⟨x.n,RationalWeightedStep.point (fraction x.q),fraction_unit x.q x.nonnegative⟩
theorem ofFn_point {n : ℕ} (p : Vector ℚ n) : List.ofFn (RationalWeightedStep.point p)=p.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp [RationalWeightedStep.point]
noncomputable def cardinalInputProgram : PolyProgram Input.encode SparseCardinalRounding.Program.encodeInput Input.cardinal :=
  fractionRow_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    rw [fractionRow_list]
    change enc ((fraction x.q).toList)=enc (List.ofFn (RationalWeightedStep.point (fraction x.q)))
    rw [ofFn_point])

def counts (x : List ℚ × List Bool) : List ℕ :=
  (SparseGraph.ListOperation.indices x.1).map (fun i => ⌊x.1[i]?.getD 0⌋₊+if x.2[i]?.getD false then 1 else 0)
@[fun_prop] theorem counts_poly : Poly counts := by unfold counts; apply list_map <;> fun_prop
 theorem counts_view {n : ℕ} (q : Fin n → ℚ) (p : Vector ℚ n) :
    counts (List.ofFn q,SparseGraph.ListOperation.setView (SparseCardinalRounding.selected p))=List.ofFn (SparseGridRounding.count q p) := by
  simp only [counts,SparseGraph.ListOperation.indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,SparseCardinalRounding.selected,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
  rfl
def post (x : List ℚ × Data (List Bool)) : Data (List ℕ) := (x.2.1,x.2.2.map (fun b => counts (x.1,b)))
@[fun_prop] theorem post_poly : Poly post := by
  unfold post; apply pair
  · fun_prop
  · apply list_map <;> fun_prop

def Input.result (x : Input) : Data (List ℕ) :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.q)).1,(law x.q).states.toList.map List.ofFn)
 theorem vector_point {n : ℕ} (p : Vector ℚ n) : Vector.ofFn (RationalWeightedStep.point p)=p := by
  ext i hi
  simp only [RationalWeightedStep.point,Vector.getElem_ofFn]
 theorem post_result (x : Input) : post (x.raw,SparseCardinalRounding.Program.result x.cardinal)=x.result := by
  have hv : Vector.ofFn x.cardinal.p = fraction x.q := vector_point (fraction x.q)
  have hr : SparseCardinalRounding.round (Vector.ofFn x.cardinal.p) = SparseCardinalRounding.round (fraction x.q) := congrArg (fun p : Vector ℚ x.n => SparseCardinalRounding.round p) hv
  simp only [post,Input.result,law,SparseCardinalRounding.Program.result,SparseGraph.Program.columnRaw,
    SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def,Input.raw,
    SparseIntegerLaw.BinarySparse.raw]
  rw [hr]
  congr 2
  funext p

  exact counts_view x.q p

noncomputable def program : PolyProgram Input.encode (enc : Data (List ℕ) → List Bool) Input.result :=
  (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)).fanout
    (cardinalInputProgram.comp SparseCardinalRounding.Program.program) |>.comp post_poly.program).congr _ post_result
end MetricKMedian.SparseGridRounding.Program
end

end OAI
