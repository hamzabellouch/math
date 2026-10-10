import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseCountFeatures
import OAI.Combinatorics.KMedian.Process.RoundingUniformStep

namespace OAI


                                           
section
namespace MetricKMedian.SparseCounts.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev Row := List ℕ
abbrev Table := List Row
abbrev er := encodeList Nat.bits
abbrev et := encodeList er

def indices {α : Type} (xs : List α) : List ℕ := List.range xs.length
@[fun_prop] theorem indices_poly {α : Type} [Coding α] [Inhabited α] : Poly (indices (α:=α)) := list_indices

def view {n m : ℕ} (G : SparseCounts.Table n m) : Table := List.ofFn (fun i => List.ofFn (G i))
def setView {n : ℕ} (S : Fin n → ℕ) : Row := List.ofFn S
def edges (x : List Unit × Table) : List ℚ :=
  (indices x.1).flatMap (fun h => x.2.map (fun col => ((col[h]?.getD 0:ℕ):ℚ)))
def featureList (x : List Unit × Table) : List ℚ := RoundingList.features (edges x)
def nextTable (x : (ℕ × Table) × Row) : Table :=
  (indices x.1.2).map (fun i => if i=x.1.1 then x.2 else x.1.2[i]?.getD [])
def dimensions (x : List Unit × List (SparseIntegerLaw.BinarySparse.Data Row)) : List Unit :=
  let bs := x.1.flatMap (fun _ => x.2.map (fun _ => (0:ℚ)))
  RoundingList.dimensions bs

@[fun_prop] theorem edges_poly : Poly edges := by
  unfold edges
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem featureList_poly : Poly featureList := by unfold featureList; fun_prop
@[fun_prop] theorem nextTable_poly : Poly nextTable := by
  unfold nextTable
  apply list_map <;> fun_prop
@[fun_prop] theorem dimensions_poly : Poly dimensions := by
  unfold dimensions
  apply comp RoundingList.dimensions_poly
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

 theorem edges_view {n m : ℕ} (G : SparseCounts.Table n m) :
    edges (List.replicate n (),view G)=List.ofFn (edgeCode G) := by
  simp only [edges,indices,List.length_replicate,RoundingList.range_finRange,view,
    List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  simp only [List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some]
  rw [RoundingList.ofFn_product]
  rfl

 theorem featureList_view {n m : ℕ} (G : SparseCounts.Table n m) :
    featureList (List.replicate n (),view G)=List.ofFn (features G) := by
  simp only [featureList,edges_view,RoundingList.features,List.flatMap_def,List.map_ofFn,
    Function.comp_def,RoundingList.ofFn_product]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i
    have hi : (Fin.castAdd ((n*m)*(n*m)) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inl i) := rfl
    change edgeCode G i = features G (Fin.castAdd ((n*m)*(n*m)) i)
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]
  · congr 1; funext i
    have hi : (Fin.natAdd (n*m) i : Fin (n*m+(n*m)*(n*m)))=finSumFinEquiv (Sum.inr i) := by apply Fin.ext; simp [finSumFinEquiv]
    rw [hi]
    simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

 theorem nextTable_view {n m : ℕ} (G : SparseCounts.Table n m) (S : Fin n → ℕ) (i : Fin m) :
    nextTable ((i.val,view G),setView S)=view (next G S i) := by
  apply List.ext_getElem
  · simp only [nextTable,indices,view,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj hj'
    have hjm : j < m := by simpa only [view,List.length_ofFn] using hj'
    simp only [nextTable,indices,view,setView,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      List.getElem?_ofFn,dite_eq_left hjm,Option.getD_some,next]
    by_cases h : j=i.val
    · have he : (⟨j,hjm⟩ : Fin m)=i := Fin.ext h
      simp only [ite_eq_left h,he,Function.update_self]
    · have he : (⟨j,hjm⟩ : Fin m)≠i := fun e => h (Fin.val_eq_of_eq e)
      simp only [ite_eq_right h,Function.update_of_ne he]

 theorem dimensions_eq {n m : ℕ} (cs : Fin m → SparseIntegerLaw.BinarySparse.Data Row) :
    dimensions (List.replicate n (),List.ofFn cs)=List.replicate (n*m+(n*m)*(n*m)) () := by
  have h : (List.replicate n ()).flatMap (fun _ => (List.ofFn cs).map (fun _ => (0:ℚ)))=
      List.ofFn (fun _ : Fin (n*m) => (0:ℚ)) := by
    simp only [List.map_const',List.length_ofFn,List.flatMap_replicate,List.ofFn_const]
    simp [List.flatten_replicate_replicate]
  simp only [dimensions,h,RoundingList.dimensions_list]
end MetricKMedian.SparseCounts.ListOperation
end

end OAI
