import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalNearestCopies
import OAI.Combinatorics.KMedian.Programs.GreedyPackingProgram

namespace OAI


                                          
section
namespace MetricKMedian.Preparation.RationalNearest.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def erase (x : ℕ × Row) : Row := (indices x.2).map (fun i => MetricKMedian.MaskProgram.get x.2 i && decide (i≠x.1))
def insert (x : ℕ × Row) : Row := (indices x.2).map (fun i => MetricKMedian.MaskProgram.get x.2 i || decide (i=x.1))
@[fun_prop] theorem erase_poly : Poly erase := by
  unfold erase
  simp only [decide_not]
  apply list_map <;> fun_prop
@[fun_prop] theorem insert_poly : Poly insert := by unfold insert; apply list_map <;> fun_prop
 theorem erase_view {n : ℕ} (U : Finset (Fin n)) (a : Fin n) : erase (a.val,setView U)=setView (U.erase a) := by
  simp only [erase,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_erase,
    Bool.decide_and]
  simp only [ne_eq,Fin.val_inj]
  exact Bool.and_comm _ _
 theorem insert_view {n : ℕ} (U : Finset (Fin n)) (a : Fin n) : insert (a.val,setView U)=setView (Insert.insert a U) := by
  simp only [insert,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_insert,Fin.ext_iff,
    Bool.decide_or]
  exact Bool.or_comm _ _

def raw : ℕ → List ℚ × Row → Row
  | 0,x => x.2.map (fun _ => false)
  | k+1,x => if x.2.any id then
      let a := MetricKMedian.MaskProgram.nearest x
      insert (a,raw k (x.1,erase (a,x.2)))
    else x.2.map (fun _ => false)
@[fun_prop] theorem raw_poly (k : ℕ) : Poly (raw k) := by
  induction k with
  | zero => change Poly (fun x : List ℚ × Row => x.2.map (fun _ => false)); apply list_map <;> fun_prop
  | succ k ih =>
    change Poly (fun x : List ℚ × Row => if x.2.any id then
      insert (MetricKMedian.MaskProgram.nearest x,raw k (x.1,erase (MetricKMedian.MaskProgram.nearest x,x.2)))
      else x.2.map (fun _ => false))
    fun_prop
 theorem raw_view {n : ℕ} (d : Fin n → ℚ) (U : Finset (Fin n)) (k : ℕ) :
    raw k (List.ofFn d,setView U)=setView (takeNearest d k U) := by
  induction k generalizing U with
  | zero => simp only [raw,takeNearest,setView,List.map_ofFn,Function.comp_def,notMem_empty,decide_false]
  | succ k ih =>
    unfold raw takeNearest
    rw [Completion.Rational.PackingProgram.any_view]
    by_cases h : U.Nonempty
    · simp only [decide_eq_true h,ite_true,dite_eq_left h]
      rw [MetricKMedian.MaskProgram.nearest_view d U h]
      have he : Preparation.firstNearest U d h=least U d h := rfl
      rw [he,erase_view,ih,insert_view]
    · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h,setView,List.map_ofFn,
        Function.comp_def,notMem_empty,decide_false]
end MetricKMedian.Preparation.RationalNearest.MaskProgram
end

end OAI
