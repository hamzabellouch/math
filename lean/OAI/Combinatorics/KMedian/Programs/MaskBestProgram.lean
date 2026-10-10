import Mathlib
import OAI.Combinatorics.KMedian.Programs.GreedyPackingProgram
import OAI.Combinatorics.KMedian.Programs.ScoreProgram
import OAI.Combinatorics.KMedian.Programs.TaggedBestProgram

namespace OAI


                                       
section
namespace MetricKMedian.Completion.Rational.BestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
def card (O : Row) : ℕ := (O.filter id).length
@[fun_prop] theorem card_poly : Poly card := by unfold card; fun_prop
 theorem card_view {f : ℕ} (O : Finset (Fin f)) : card (setView O)=O.card := by
  exact EncodingLists.bool_card O

def good (x : ℚ × Row) : Bool := x.2.any id && decide ((card x.2:ℚ)≤x.1)
@[fun_prop] theorem good_poly : Poly good := by unfold good; fun_prop
 theorem good_view {f : ℕ} (B : ℚ) (O : Finset (Fin f)) :
    good (B,setView O)=decide (O.Nonempty ∧ (O.card:ℚ)≤B) := by
  simp only [good,PackingProgram.any_view,card_view,Bool.decide_and]

def annotate (x : (ℚ × List (List ℚ)) × Table) : List SparseSelect.TaggedProgram.Tag :=
  x.2.map (fun O => (good (x.1.1,O),(ScoreProgram.raw (x.1.2,O),O)))
@[fun_prop] theorem annotate_poly : Poly annotate := by unfold annotate; apply list_map <;> fun_prop

def raw (x : (ℚ × List (List ℚ)) × Table) : Table := SparseSelect.TaggedProgram.raw (annotate x)
@[fun_prop] theorem raw_poly : Poly raw := by unfold raw; fun_prop
 theorem raw_best {f j : ℕ} (B : ℚ) (d : Fin j → Fin f → ℚ) (L : List (Finset (Fin f))) :
    raw ((B,List.ofFn (fun c => List.ofFn (d c))),L.map setView)=
      ((SparseSelect.best (fun O => decide (O.Nonempty ∧ (O.card:ℚ)≤B)) (score d) L).map setView).toList := by
  let ann := fun O : Finset (Fin f) => (decide (O.Nonempty ∧ (O.card:ℚ)≤B),(score d O,setView O))
  have ha : annotate ((B,List.ofFn (fun c => List.ofFn (d c))),L.map setView)=L.map ann := by
    simp only [annotate,List.map_map,Function.comp_def,good_view,ScoreProgram.raw_score]
    rfl
  unfold raw
  rw [ha,SparseSelect.TaggedProgram.raw_best]
  rw [← SparseSelect.best_map (fun O => decide (O.Nonempty ∧ (O.card:ℚ)≤B)) (score d)
    Prod.fst (fun a => a.2.1) ann (fun _ => rfl) (fun _ => rfl)]
  simp only [Option.map_map]
  rfl
end MetricKMedian.Completion.Rational.BestProgram
end

end OAI
