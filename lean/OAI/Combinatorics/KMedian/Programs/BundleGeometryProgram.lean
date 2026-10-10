import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Programs.GreedyPackingProgram
import OAI.Combinatorics.KMedian.Geometry.RationalBundleGeometry

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalBundles.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
abbrev Raw := (List (List ℚ) × List (List ℚ)) × (Table × List ℚ)
def view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) : Raw :=
  ((List.ofFn (fun i => List.ofFn (d i)),List.ofFn (fun i => List.ofFn (di i))),
    (List.ofFn (fun i => setView (F i)),List.ofFn y))
def neighborMask (x : List ℚ × ℕ) : Row := (indices x.1).map (fun i => decide (i≠x.2))
@[fun_prop] theorem neighborMask_poly : Poly neighborMask := by unfold neighborMask; simp only [decide_not]; apply list_map <;> fun_prop
 theorem neighborMask_view {n : ℕ} (ds : Fin n → ℚ) (t : Fin n) :
    neighborMask (List.ofFn ds,t.val)=setView (univ.erase t) := by
  simp only [neighborMask,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,setView,mem_erase,mem_univ,and_true]
  simp only [ne_eq,Fin.val_inj]
def nextData (x : List ℚ × ℕ) : ℕ := if (neighborMask x).any id then MetricKMedian.MaskProgram.nearest (x.1,neighborMask x) else x.2
@[fun_prop] theorem nextData_poly : Poly nextData := by unfold nextData; fun_prop
 theorem nextData_view {n : ℕ} (d : Fin n → Fin n → ℚ) (t : Fin n) :
     nextData (List.ofFn (d t),t.val)=(next d t).val := by
  unfold nextData
  rw [neighborMask_view,Completion.Rational.PackingProgram.any_view]
  simp only [decide_eq_true_eq]
  unfold next
  split_ifs with h
  · rw [MetricKMedian.MaskProgram.nearest_view]
  · rfl

def bundleData (δ : ℚ) (x : Raw × ℕ) : Row :=
  let t := x.2
  let s := nextData (x.1.1.1[t]?.getD [],t)
  if s=t then x.1.2.1[t]?.getD [] else
    (indices x.1.2.2).map (fun a => MetricKMedian.MaskProgram.get (x.1.2.1[t]?.getD []) a &&
      decide ((x.1.1.2[t]?.getD [])[a]?.getD 0 ≤ δ*(x.1.1.1[t]?.getD [])[s]?.getD 0))
@[fun_prop] theorem bundleData_poly (δ : ℚ) : Poly (bundleData δ) := by
  unfold bundleData
  apply ite_prop
  · fun_prop
  · fun_prop
  · apply list_map <;> fun_prop
 theorem bundleData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) (t : Fin n) :
    bundleData δ (view d di F y,t.val)=setView (bundle d di F δ t) := by
  simp only [bundleData,view,List.getElem?_ofFn,dite_eq_left t.isLt,Option.getD_some,Fin.eta,nextData_view]
  by_cases h : next d t=t
  · simp only [h,ite_true,bundle]
  · have hn : (next d t).val≠t.val := fun hh => h (Fin.ext hh)
    simp only [hn,ite_false,bundle,h,indices,List.length_ofFn,RoundingList.range_finRange,
      ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,
      dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,setView,mem_filter,Bool.decide_and]

def bundlesData (δ : ℚ) (x : Raw) : Table := (indices x.2.1).map (fun t => bundleData δ (x,t))
@[fun_prop] theorem bundlesData_poly (δ : ℚ) : Poly (bundlesData δ) := by unfold bundlesData; apply list_map <;> fun_prop
 theorem bundlesData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) :
    bundlesData δ (view d di F y)=List.ofFn (fun t => setView (bundle d di F δ t)) := by
  unfold bundlesData
  simp only [view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun t : Fin n => bundleData δ (view d di F y,t.val))=_
  simp only [bundleData_view]

def missingData (δ : ℚ) (x : Raw) : Table := (indices x.2.1).map (fun t =>
    (indices x.2.2).map (fun a => MetricKMedian.MaskProgram.get (x.2.1[t]?.getD []) a && !MetricKMedian.MaskProgram.get (bundleData δ (x,t)) a))
@[fun_prop] theorem missingData_poly (δ : ℚ) : Poly (missingData δ) := by
  unfold missingData; apply list_map
  · apply list_map <;> fun_prop
  · fun_prop
 theorem missingData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) :
    missingData δ (view d di F y)=List.ofFn (fun t => setView (missing d di F δ t)) := by
  unfold missingData
  simp only [view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun t : Fin n => List.ofFn (fun a : Fin f => MetricKMedian.MaskProgram.get ((List.ofFn (fun t => setView (F t)))[t.val]?.getD []) a.val && !MetricKMedian.MaskProgram.get (bundleData δ (view d di F y,t.val)) a.val))=_
  simp only [bundleData_view,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,missing,mem_sdiff,Bool.decide_and,decide_not]

def massData (x : List ℚ × Table) : List ℚ := x.2.map (fun P =>
  ((indices x.1).map (fun i => if MetricKMedian.MaskProgram.get P i then x.1[i]?.getD 0 else 0)).sum)
@[fun_prop] theorem massData_poly : Poly massData := by
  unfold massData
  apply list_map
  · apply comp rat_sum
    apply list_map <;> fun_prop
  · fun_prop
 theorem massData_view {f n : ℕ} (y : Fin f → ℚ) (P : Fin n → Finset (Fin f)) :
    massData (List.ofFn y,List.ofFn (fun t => setView (P t)))=List.ofFn (mass y P) := by
  simp only [massData,List.map_ofFn,Function.comp_def,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,decide_eq_true_eq,List.sum_ofFn,← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rfl
end MetricKMedian.Preparation.RationalBundles.Program
end

end OAI
