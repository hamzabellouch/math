import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparsePhysicalBatch
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Geometry.GraphListOperations

namespace OAI


                                         
section
namespace MetricKMedian.SparsePhysicalBatch.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table er et indices)

abbrev Raw := (Row × Table) × (ℚ × List ℚ)

def conflictFree (x : Table × Row) (e : ℕ) : Bool :=
  ((indices x.2).map (fun f => !(x.1[e]?.getD [])[f]?.getD false || !(x.2[f]?.getD false))).all id

def select (bal : Bool) (x : Raw × Row) : Row :=
  (indices x.2).map (fun e =>
    if bal then x.2[e]?.getD false && conflictFree (x.1.1.2,x.2) e && (x.1.1.1[e]?.getD false)
    else x.2[e]?.getD false && !(x.1.1.1[e]?.getD false))

@[fun_prop] theorem conflictFree_poly : Poly (fun x : (Table × Row) × ℕ => conflictFree x.1 x.2) := by
  unfold conflictFree
  apply comp bool_all
  apply list_map <;> fun_prop
@[fun_prop] theorem select_poly (bal : Bool) : Poly (select bal) := by
  unfold select
  apply list_map <;> fun_prop

 theorem conflictFree_view {n : ℕ} (C : Fin n → Finset (Fin n)) (ω : Fin n → Bool) (e : Fin n) :
    conflictFree (List.ofFn (fun a => SparseGraph.ListOperation.setView (C a)),List.ofFn ω) e.val=true ↔
      ∀ f∈C e, ω f=false := by
  simp only [conflictFree,indices,List.length_ofFn,RoundingList.range_finRange,List.map_map,
    Function.comp_def,List.all_map,List.all_eq_true,List.mem_finRange,forall_const,
    SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,id_eq,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not]
  constructor
  · intro h f hf
    exact (h f).resolve_left (not_not.mpr hf)
  · intro h f
    by_cases hf : f∈C e
    · exact Or.inr (h f hf)
    · exact Or.inl hf

 theorem select_view {n : ℕ} (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (ω : Fin n → Bool) (bal : Bool) :
    select bal (((SparseGraph.ListOperation.setView Z,List.ofFn (fun a => SparseGraph.ListOperation.setView (C a))),
      (p,List.ofFn q)),List.ofFn ω)=SparseGraph.ListOperation.setView
      (if bal then balanced Z C ω else unbalanced Z ω) := by
  apply List.ext_getElem
  · simp only [select,indices,List.length_ofFn,List.length_map,List.length_range,
      SparseGraph.ListOperation.setView]
  · intro i hi hi'
    have hin : i<n := by simpa only [SparseGraph.ListOperation.setView,List.length_ofFn] using hi'
    simp only [select,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left hin,Option.getD_some]
    apply Bool.eq_iff_iff.mpr
    cases bal
    · simp only [Bool.false_eq_true,ite_false,unbalanced,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,decide_eq_true_eq]
    · simp only [ite_true,balanced,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true,decide_eq_true_eq]
      rw [show conflictFree (List.ofFn (fun a => List.ofFn (fun h => decide (h∈C a))),List.ofFn ω) i=true ↔
        ∀ f∈C ⟨i,hin⟩, ω f=false from conflictFree_view C ω ⟨i,hin⟩]
end MetricKMedian.SparsePhysicalBatch.ListOperation
end

end OAI
