import Mathlib
import OAI.Combinatorics.KMedian.Geometry.ListSigma
import OAI.Combinatorics.KMedian.Programs.MaximumProgram
import OAI.Combinatorics.KMedian.Programs.RationalSortProgram
import OAI.Combinatorics.KMedian.Geometry.RationalSplitEnumeration

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalSplitting.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Raw := List ℚ × List (List ℚ)
def view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) : Raw :=
  (List.ofFn y,List.ofFn (fun c => List.ofFn (x c)))
def cutsData (x : Raw × ℕ) : List ℚ :=
  RationalSortProgram.sort ((x.1.1[x.2]?.getD 0 :: x.1.2.map (fun r => r[x.2]?.getD 0)).filter (fun q => decide (0<q)))
@[fun_prop] theorem cutsData_poly : Poly cutsData := by
  unfold cutsData
  apply comp RationalSortProgram.sort_poly
  apply list_filter
  · fun_prop
  · have h : Poly (fun x : Raw × ℕ => x.1.2.map (fun r => r[x.2]?.getD 0)) := by apply list_map <;> fun_prop
    have g : Poly (fun x : Raw × ℕ => x.1.1[x.2]?.getD (0:ℚ)) := by fun_prop
    exact Poly.comp list_cons (pair g h)
 theorem cutsData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (i : Fin f) :
    cutsData (view y x,i.val)=(cuts y x i).sort := by
  simp only [cutsData,view,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
    List.map_ofFn,Function.comp_def,RationalSortProgram.sort_eq,List.toFinset_filter,List.toFinset_cons]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_insert,List.mem_toFinset,List.mem_ofFn,cuts,Finset.mem_image,
    Finset.mem_univ,true_and,decide_eq_true_eq]

def piecesData (x : Raw) : List (ℕ × ℚ) :=
  (indices x.1).flatMap (fun i => (cutsData (x,i)).map (fun q => (i,q)))
@[fun_prop] theorem piecesData_poly : Poly piecesData := by
  unfold piecesData
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
 theorem piecesData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    piecesData (view y x)=List.ofFn (fun a => ((index y x a).1.val,(index y x a).2.val)) := by
  simp only [piecesData,view,indices,List.length_ofFn,RoundingList.range_finRange,List.flatMap_map]
  change ((List.finRange f).flatMap (fun i => (cutsData (view y x,i.val)).map (fun q => (i.val,q))))=_
  simp only [cutsData_view]
  have hs (i : Fin f) : (cuts y x i).sort=List.ofFn (fun t => ((cuts y x i).orderIsoOfFin rfl t).val) := by
    exact (EncodingLists.sorted_enum (cuts y x i)).symm
  simp only [hs,List.map_ofFn,Function.comp_def,List.flatMap_def,← List.ofFn_eq_map]
  rw [ListSigma.ofFn_sigma]
  rfl

def originalData (x : Raw) : List ℕ := (piecesData x).map Prod.fst
@[fun_prop] theorem originalData_poly : Poly originalData := by unfold originalData; apply list_map <;> fun_prop
 theorem originalData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    originalData (view y x)=List.ofFn (fun a => (original y x a).val) := by
  simp only [originalData,piecesData_view,List.map_ofFn,Function.comp_def,original]

def previousData (x : List ℚ × ℚ) : ℚ := maximum (0::x.1.filter (fun q => decide (q<x.2)))
@[fun_prop] theorem previousData_poly : Poly previousData := by
  unfold previousData
  have h : Poly (fun x : List ℚ × ℚ => x.1.filter (fun q => decide (q<x.2))) := by apply list_filter <;> fun_prop
  have h2 : Poly (fun x : List ℚ × ℚ => (0:ℚ)::x.1.filter (fun q => decide (q<x.2))) :=
    Poly.comp (f:=fun t : ℚ × List ℚ => t.1::t.2) (list_cons (α:=ℚ)) (pair (const (α:=List ℚ × ℚ) (0:ℚ)) h)
  exact Poly.comp maximum_poly h2
 theorem previousData_view (s : Finset ℚ) (q : ℚ) : previousData (s.sort,q)=RationalIntervals.previous s q := by
  apply maximum_eq_finset
  · exact insert_nonempty _ _
  intro a
  simp only [List.mem_cons,List.mem_filter,mem_sort,decide_eq_true_eq,mem_insert,mem_filter]

def weightsData (x : Raw) : List ℚ := (piecesData x).map (fun a => a.2-previousData (cutsData (x,a.1),a.2))
@[fun_prop] theorem weightsData_poly : Poly weightsData := by unfold weightsData; apply list_map <;> fun_prop
 theorem weightsData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    weightsData (view y x)=List.ofFn (weights y x) := by
  rw [weightsData,piecesData_view,List.map_ofFn]
  simp only [Function.comp_def,cutsData_view,previousData_view]
  rfl

def assignedData (x : Raw) : Table := x.2.map (fun row => (piecesData x).map (fun a => decide (a.2≤row[a.1]?.getD 0)))
@[fun_prop] theorem assignedData_poly : Poly assignedData := by
  unfold assignedData
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop
 theorem assignedData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    assignedData (view y x)=List.ofFn (fun c => setView (assigned y x c)) := by
  unfold assignedData
  rw [piecesData_view]
  simp only [view,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,setView,mem_assigned,assignment,mem_filter,mem_univ,true_and]
end MetricKMedian.Preparation.RationalSplitting.Program
end

end OAI
