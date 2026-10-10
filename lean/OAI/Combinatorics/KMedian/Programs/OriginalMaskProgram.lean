import Mathlib
import OAI.Combinatorics.KMedian.Programs.FinsetMaskProgram

namespace OAI


                                           
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView indices)

def imageRaw (x : (List Unit × List ℕ) × Row) : Row :=
  (indices x.1.1).map (fun h => ((indices x.1.2).map (fun i =>
    get x.2 i && decide (x.1.2[i]?.getD 0=h))).any id)
@[fun_prop] theorem imageRaw_poly : Poly imageRaw := by
  unfold imageRaw
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem imageRaw_view {f h : ℕ} (orig : Fin f → Fin h) (O : Finset (Fin f)) :
    imageRaw ((List.replicate h (),List.ofFn (fun i => (orig i).val)),setView O)=setView (O.image orig) := by
  simp only [imageRaw,indices,List.length_replicate,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  unfold setView
  apply congrArg List.ofFn
  funext a
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,id_eq,get,List.getElem?_ofFn,
    dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq,mem_image]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    exact ⟨i,hi.1,Fin.ext hi.2⟩
  · rintro ⟨i,hi,he⟩
    refine ⟨_,⟨i,rfl⟩,?_⟩
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hi,congrArg Fin.val he⟩

def pullback (x : List ℚ × List ℕ) : List ℚ := x.2.map (fun i => x.1[i]?.getD 0)
@[fun_prop] theorem pullback_poly : Poly pullback := by unfold pullback; apply list_map <;> fun_prop
 theorem pullback_view {f h : ℕ} (orig : Fin f → Fin h) (d : Fin h → ℚ) :
    pullback (List.ofFn d,List.ofFn (fun i => (orig i).val))=List.ofFn (fun i => d (orig i)) := by
  simp only [pullback,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

def pullbackMatrix (x : List (List ℚ) × List ℕ) : List (List ℚ) :=
  x.2.map (fun i => pullback (x.1[i]?.getD [],x.2))
@[fun_prop] theorem pullbackMatrix_poly : Poly pullbackMatrix := by unfold pullbackMatrix; apply list_map <;> fun_prop
 theorem pullbackMatrix_view {f h : ℕ} (orig : Fin f → Fin h) (d : Fin h → Fin h → ℚ) :
    pullbackMatrix (List.ofFn (fun i => List.ofFn (d i)),List.ofFn (fun i => (orig i).val))=
      List.ofFn (fun i => List.ofFn (fun k => d (orig i) (orig k))) := by
  simp only [pullbackMatrix,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,pullback_view]
end MetricKMedian.MaskProgram
end

end OAI
