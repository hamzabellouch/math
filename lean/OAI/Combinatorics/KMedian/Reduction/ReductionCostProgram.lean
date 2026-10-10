import Mathlib
import OAI.Combinatorics.KMedian.Programs.InstanceDataProgram

namespace OAI


                                            
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MaskProgram

def nearestData (x : List ℚ × Row) : ℚ := LPBinary.minimum (selectedValues x)
@[fun_prop] theorem nearestData_poly : Poly nearestData := by
  have h : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  unfold nearestData; fun_prop
 theorem nearestData_view (I : Instance) (j : Fin I.n) (U : Finset (Fin I.n)) :
    nearestData (List.ofFn (I.distance j),setView U)=rationalNearest I j U := by
  unfold nearestData rationalNearest
  split_ifs with h
  · exact LPBinary.minimum_eq_finset _ _ (h.image _) (selectedValues_mem (I.distance j) U)
  · have he : selectedValues (List.ofFn (I.distance j),setView U)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      obtain ⟨i,hi,_⟩ := mem_image.mp ((selectedValues_mem (I.distance j) U q).mp hq)
      exact h ⟨i,hi⟩
    rw [he]; rfl

def costData (x : Raw × Row) : ℚ :=
  ((indices x.1.1.1).map (fun j => if get x.1.1.1 j then nearestData (x.1.2.2[j]?.getD [],x.2) else 0)).sum
@[fun_prop] theorem costData_poly : Poly costData := by
  unfold costData
  apply comp rat_sum
  apply list_map <;> fun_prop
 theorem costData_view (I : Instance) (U : Finset (Fin I.n)) : costData (view I,setView U)=rationalCost I U := by
  simp only [costData,view,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,
    MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq]
  change (List.ofFn (fun j : Fin I.n => if j∈I.clients then nearestData (List.ofFn (I.distance j),setView U) else 0)).sum=_
  simp only [nearestData_view,List.sum_ofFn,rationalCost]
  rw [← Finset.sum_filter]
  simp only [filter_mem_eq_inter,univ_inter]

def diff (x : Row × Row) : Row := (x.1.zip x.2).map (fun z => z.1 && !z.2)
def union (x : Row × Row) : Row := (x.1.zip x.2).map (fun z => z.1 || z.2)
@[fun_prop] theorem diff_poly : Poly diff := by unfold diff; apply list_map <;> fun_prop
@[fun_prop] theorem union_poly : Poly union := by unfold union; apply list_map <;> fun_prop
 theorem diff_view {n : ℕ} (S T : Finset (Fin n)) : diff (setView S,setView T)=setView (S\T) := by
  simp only [diff,setView,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,mem_sdiff,Bool.decide_and,decide_not]
 theorem union_view {n : ℕ} (S T : Finset (Fin n)) : union (setView S,setView T)=setView (S∪T) := by
  simp only [union,setView,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,mem_union,Bool.decide_or]
end MetricKMedian.Reduction.Program
end

end OAI
