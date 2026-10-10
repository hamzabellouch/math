import Mathlib

namespace OAI


                                          
section
namespace MetricKMedian.EncodingLists
open Finset

theorem sorted_enum {α : Type} [LinearOrder α] (s : Finset α) :
    List.ofFn (fun i : Fin s.card => (s.orderIsoOfFin rfl i).val)=s.sort := by
  rw [List.ofFn_eq_map]
  exact s.listMap_orderEmbOfFin_finRange rfl

theorem filter_range {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (List.finRange n).filter (fun i => decide (p i))=(univ.filter p).sort := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · exact (univ.filter p).sortedLT_sort
  · intro i
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,mem_sort,mem_filter,mem_univ]

theorem map_filter_enum {n : ℕ} {α : Type} (f : Fin n → α) (p : Fin n → Prop) [DecidablePred p] :
    ((List.finRange n).filter (fun i => decide (p i))).map f =
      List.ofFn (fun i : Fin (univ.filter p).card => f ((univ.filter p).orderIsoOfFin rfl i).val) := by
  rw [filter_range,← sorted_enum,List.map_ofFn]
  rfl

end MetricKMedian.EncodingLists
end

end OAI
