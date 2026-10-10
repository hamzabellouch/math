import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.BoolPrograms
import OAI.Combinatorics.ThinTrees.Encoding.OrderedGraph
import OAI.Combinatorics.ThinTrees.Sparsification.Realization

namespace OAI

/-! Selection realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Finset
open AlgorithmicThinTrees.OrderedGraph

variable {α : Type*}

def maskEntry (ea : α → Word) : Realizes (prodCode boolCode ea) (listCode ea)
    (fun p => if p.1 then [p.2] else []) :=
  (first boolCode ea).ite ((second boolCode ea).then (singleton ea))
    (constant (prodCode boolCode ea) (listCode ea) [])
instance poly_maskEntry (ea : α → Word) : PolyTime (maskEntry ea) := by unfold maskEntry;infer_instance

def maskArray (ea : α → Word) (z : α) : Realizes (prodCode boolsCode (listCode ea)) (listCode ea)
    (fun p => (zipDefault (fun q : Bool×α => if q.1 then [q.2] else []) false z p).flatten) :=
  ((maskEntry ea).zipWith false z).then (joinList ea)
instance poly_maskArray (ea : α → Word) (z : α) : PolyTime (maskArray ea z) := by
  unfold maskArray;infer_instance

lemma sorted_selected {m : ℕ} (A : Finset (Fin m)) :
    (List.finRange m).filter (fun e => decide (e ∈ A))=List.ofFn (edgeEmbedding A) := by
  have hh : (List.ofFn (edgeEmbedding A))=A.sort (· ≤ ·) := by
    rw [List.ofFn_eq_map]
    exact A.listMap_orderEmbOfFin_finRange rfl
  rw [hh]
  apply ((List.sortedLT_finRange m).pairwise.filter _).sortedLT.eq_of_mem_iff A.sortedLT_sort
  intro e
  simp

lemma maskArray_data {m : ℕ} (A : Finset (Fin m)) (f : Fin m → α) (z : α) :
    (zipDefault (fun q : Bool×α => if q.1 then [q.2] else []) false z
      (List.ofFn (fun e => decide (e ∈ A)),List.ofFn f)).flatten=
        List.ofFn (fun i => f (edgeEmbedding A i)) := by
  rw [zipDefault_ofFn]
  have hh : ∀es : List (Fin m),
      (es.map (fun e => if decide (e ∈ A) then [f e] else [])).flatten=
        (es.filter (fun e => decide (e ∈ A))).map f := by
    intro es
    induction es with
    | nil => rfl
    | cons e es ih => by_cases he : e ∈ A <;> simp_all
  dsimp only
  rw [List.ofFn_eq_map,hh,sorted_selected,List.map_ofFn]
  rfl

lemma selected_sublist {m : ℕ} (A : Finset (Fin m)) (f : Fin m → α) :
    (List.ofFn (fun i => f (edgeEmbedding A i))).Sublist (List.ofFn f) := by
  change (List.ofFn (f ∘ edgeEmbedding A)).Sublist (List.ofFn f)
  rw [←List.map_ofFn,←sorted_selected,List.ofFn_eq_map (f:=f)]
  exact List.Sublist.map f (List.filter_sublist)

lemma listCode_sublist_le {ea : α → Word} {xs ys : List α} (h : xs.Sublist ys) :
    (listCode ea xs).length≤(listCode ea ys).length := by
  rw [len_listCode,len_listCode]
  exact (h.map (fun x => 2*(ea x).length+1)).sum_le_sum (fun _ _ => Nat.zero_le _)

lemma listCode_selected_le {m : ℕ} (ea : α → Word) (A : Finset (Fin m)) (f : Fin m → α) :
    (listCode ea (List.ofFn (fun i => f (edgeEmbedding A i)))).length≤
      (listCode ea (List.ofFn f)).length := listCode_sublist_le (selected_sublist A f)

end CurrentKS.Realization
end

end OAI
