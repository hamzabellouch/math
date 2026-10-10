import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic

namespace OAI


                                             
section
namespace MetricKMedian.Binary.Automatic.Poly
open PolyProgram
@[fun_prop] theorem bool_any : Poly (fun xs : List Bool => xs.any id) := ⟨listAny (PolyProgram.identity _) false⟩
@[fun_prop] theorem list_take {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem list_drop {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩

def natMember (x : List ℕ × ℕ) : Bool := (x.1.map (fun a => decide (a=x.2))).any id
@[fun_prop] theorem natMember_poly : Poly natMember := by
  unfold natMember
  apply comp bool_any
  apply list_map <;> fun_prop
@[simp] theorem natMember_true (xs : List ℕ) (i : ℕ) : natMember (xs,i)=true ↔ i∈xs := by
  simp only [natMember,List.any_map,List.any_eq_true,id_eq,Function.comp_def,decide_eq_true_eq]
  simp only [exists_eq_right]
end MetricKMedian.Binary.Automatic.Poly

namespace MetricKMedian.EncodingLists
open Finset
 theorem length_filter_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp
 theorem bool_card {n : ℕ} (s : Finset (Fin n)) :
    ((List.ofFn fun i => decide (i∈s)).filter id).length=s.card := by
  rw [length_filter_ofFn]
  simp
end MetricKMedian.EncodingLists
end

end OAI
