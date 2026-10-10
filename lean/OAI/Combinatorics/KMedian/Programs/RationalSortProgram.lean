import Mathlib
import OAI.Combinatorics.KMedian.Preparation.SupplierListOperations

namespace OAI


                                           
section
namespace MetricKMedian.RationalSortProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly

def insertData (x : List ℚ × ℚ) : List ℚ :=
  x.1.filter (fun a => decide (a<x.2)) ++ x.2::x.1.filter (fun a => decide (x.2<a))
@[fun_prop] theorem insertData_poly : Poly insertData := by
  unfold insertData
  apply Preparation.RationalSuppliers.Program.append_poly
  · apply list_filter <;> fun_prop
  · have hf : Poly (fun x : List ℚ × ℚ => x.1.filter (fun a => decide (x.2<a))) := by apply list_filter <;> fun_prop
    exact comp list_cons (pair (by fun_prop) hf)
 theorem filters_length {α : Type} (e : α → List Bool) (p q : α → Bool)
    (hd : ∀ a, ¬(p a=true ∧ q a=true)) (xs : List α) :
    (encodeList e (xs.filter p)).length+(encodeList e (xs.filter q)).length≤(encodeList e xs).length := by
  induction xs with
  | nil => simp [encodeList]
  | cons a xs ih =>
    have hh := hd a
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons,hp,hq,Bool.false_eq_true,ite_false,ite_true,
        EncodedList.cons_length] at ⊢
    · exact ih.trans (Nat.le_add_left _ _)
    · omega
    · omega
    · exact False.elim (hh ⟨hp,hq⟩)
 theorem insertData_length (xs : List ℚ) (a : ℚ) :
    (enc (insertData (xs,a))).length≤(enc xs).length+1*(2*(enc a).length+1) := by
  have hh := filters_length Ratio.encode (fun q : ℚ => decide (q<a)) (fun q => decide (a<q))
    (fun q h => (lt_asymm (of_decide_eq_true h.1) (of_decide_eq_true h.2))) xs
  simp only [insertData,enc,Coding.encode,EncodedList.append,List.length_append,EncodedList.cons_length,one_mul]
  change (encodeList Ratio.encode _).length+ (2*(Ratio.encode _).length+1+(encodeList Ratio.encode _).length)≤_
  omega

def sort (xs : List ℚ) : List ℚ := xs.foldl (fun s a => insertData (s,a)) []
noncomputable def foldProgram : PolyProgram (enc : List ℚ × List ℚ → List Bool) enc
    (fun x => x.1.foldl (fun s a => insertData (s,a)) x.2) :=
  insertData_poly.program.listFoldLinear 0 1 insertData_length
@[fun_prop] theorem sort_poly : Poly sort := by
  refine ⟨(((identity enc).fanout (constant enc enc ([] : List ℚ))).comp foldProgram).congr _ (fun _ => rfl)⟩

 theorem insertData_sorted (xs : List ℚ) (hx : xs.SortedLT) (a : ℚ) : (insertData (xs,a)).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  rw [insertData,List.pairwise_append,List.pairwise_cons]
  refine ⟨hx.pairwise.filter _,⟨?_,hx.pairwise.filter _⟩,?_⟩
  · intro b hb
    exact of_decide_eq_true (List.mem_filter.mp hb).2
  · intro b hb c hc
    have hb' : b<a := of_decide_eq_true (List.mem_filter.mp hb).2
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hb'
    · exact hb'.trans (of_decide_eq_true (List.mem_filter.mp hc).2)
 theorem insertData_mem (xs : List ℚ) (a q : ℚ) : q∈insertData (xs,a) ↔ q=a ∨ q∈xs := by
  simp only [insertData,List.mem_append,List.mem_filter,List.mem_cons,decide_eq_true_eq]
  constructor
  · tauto
  · rintro (rfl | hq)
    · tauto
    · rcases lt_trichotomy q a with h | h | h <;> tauto
 theorem insertData_sort (Q : Finset ℚ) (a : ℚ) : insertData (Q.sort,a) = (insert a Q).sort := by
  apply List.SortedLT.eq_of_mem_iff
  · exact insertData_sorted Q.sort Q.sortedLT_sort a
  · exact (insert a Q).sortedLT_sort
  · intro q
    simp only [insertData_mem,mem_sort,mem_insert]
 theorem fold_sort (xs : List ℚ) (Q : Finset ℚ) :
     xs.foldl (fun s a => insertData (s,a)) Q.sort=(xs.toFinset ∪ Q).sort := by
  induction xs generalizing Q with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,insertData_sort,ih]
    congr 1
    ext q
    simp only [List.toFinset_cons,mem_union,mem_insert]
    tauto
 theorem sort_eq (xs : List ℚ) : sort xs=xs.toFinset.sort := by
  have h := fold_sort xs ∅
  simpa only [sort,Finset.sort_empty,union_empty] using h
end MetricKMedian.RationalSortProgram
end

end OAI
