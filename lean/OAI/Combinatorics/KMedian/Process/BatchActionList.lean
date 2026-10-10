import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchActionCodes
import OAI.Combinatorics.KMedian.Geometry.GraphListOperations
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras

namespace OAI


                                       
section
namespace MetricKMedian.RationalBatchData.ActionList
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
abbrev Raw := Table × Row

def view {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) : Raw :=
  (List.ofFn fun h => setView (Full.erase h),setView H)
def parent (n c : ℕ) : ℕ := if c<n then c else (c-n)/n
def child (n c : ℕ) : ℕ := (c-n)%n
def valid (x : Raw) (c : ℕ) : Bool :=
  if c<x.2.length then !(x.2[c]?.getD false)
  else (x.2[parent x.2.length c]?.getD false) &&
    ((x.1[parent x.2.length c]?.getD [])[child x.2.length c]?.getD false)
def units (x : Raw) : List Unit :=
  x.2.map (fun _ => ()) ++ x.2.flatMap (fun _ => x.2.map (fun _ => ()))
def codes (x : Raw) : List ℕ := (indices (units x)).filter (valid x)

@[fun_prop] theorem parent_poly : Poly (fun x : ℕ × ℕ => parent x.1 x.2) := by unfold parent; fun_prop
@[fun_prop] theorem child_poly : Poly (fun x : ℕ × ℕ => child x.1 x.2) := by unfold child; fun_prop
@[fun_prop] theorem valid_poly : Poly (fun x : Raw × ℕ => valid x.1 x.2) := by unfold valid; fun_prop
@[fun_prop] theorem units_poly : Poly units := by
  unfold units
  apply comp (g:=fun x : Raw => (x.2.map (fun _ => ()),x.2.flatMap (fun _ => x.2.map (fun _ => ())))) Poly.list_append
  apply Poly.pair
  · apply list_map <;> fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
@[fun_prop] theorem codes_poly : Poly codes := by unfold codes; apply list_filter <;> fun_prop

 theorem units_length {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) :
    (units (view Full H)).length=n+n*n := by
  simp [units,view,setView,List.length_flatMap,Function.comp_def]

 theorem parent_code {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n))
    (e : HeavyAction Full H) : parent n (ActionCodes.code Full H e)=(heavyParent Full H e).val := by
  cases e with
  | inl e => simp only [parent,ActionCodes.code,Fin.isLt,ite_true,heavyParent]
  | inr e =>
    have hn : 0<n := Nat.zero_lt_of_lt e.val.1.isLt
    have hi : e.val.2.val<n := e.val.2.isLt
    have hc : ¬ n+e.val.1.val*n+e.val.2.val<n := by omega
    change parent n (n+e.val.1.val*n+e.val.2.val)=e.val.1.val
    rw [parent,ite_eq_right hc,Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm e.val.1.val n,
      Nat.mul_add_div hn,Nat.div_eq_of_lt hi,Nat.add_zero]
 theorem child_code {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n))
    (e : {p : Fin n × Fin n // p.1∈H ∧ p.2∈Full.erase p.1}) :
    child n (ActionCodes.code Full H (.inr e))=e.val.2.val := by
  simp only [child,ActionCodes.code]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt e.val.2.isLt]

 theorem valid_code {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n))
    (e : HeavyAction Full H) : valid (view Full H) (ActionCodes.code Full H e)=true := by
  have hp := parent_code Full H e
  cases e with
  | inl e =>
    change valid (view Full H) e.val.val=true
    simp only [valid,view,setView,List.length_ofFn,ite_eq_left e.val.isLt,
      List.getElem?_ofFn,dite_eq_left e.val.isLt,Option.getD_some,Fin.eta,
      Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not]
    exact e.property
  | inr e =>
    have hc : ¬ n+e.val.1.val*n+e.val.2.val<n := by omega
    change valid (view Full H) (n+e.val.1.val*n+e.val.2.val)=true
    simp only [valid,view,setView,List.length_ofFn,ite_eq_right hc]
    rw [show parent n (n+e.val.1.val*n+e.val.2.val)=e.val.1.val from hp,
      show child n (n+e.val.1.val*n+e.val.2.val)=e.val.2.val from child_code Full H e]
    simp only [List.getElem?_ofFn,dite_eq_left e.val.1.isLt,dite_eq_left e.val.2.isLt,Option.getD_some,Fin.eta,
      decide_eq_true e.property.1,decide_eq_true e.property.2,Bool.and_self]

 theorem mem_codes {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) (c : ℕ) :
    c∈codes (view Full H) ↔ ∃ e, ActionCodes.code Full H e=c := by
  simp only [codes,indices,units_length,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨hc,hv⟩
    by_cases hl : c<n
    · simp only [valid,view,setView,List.length_ofFn,ite_eq_left hl,List.getElem?_ofFn,dite_eq_left hl,
        Option.getD_some,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not] at hv
      exact ⟨.inl ⟨⟨c,hl⟩,hv⟩,rfl⟩
    · have hn : 0<n := by nlinarith
      have hq : (c-n)/n<n := (Nat.div_lt_iff_lt_mul hn).mpr (by omega)
      have hr : (c-n)%n<n := Nat.mod_lt _ hn
      simp only [valid,view,setView,List.length_ofFn,parent,ite_eq_right hl,child,
        List.getElem?_ofFn,dite_eq_left hq,dite_eq_left hr,Option.getD_some,Bool.and_eq_true,
        decide_eq_true_eq] at hv
      refine ⟨.inr ⟨(⟨(c-n)/n,hq⟩,⟨(c-n)%n,hr⟩),hv⟩,?_⟩
      simp only [ActionCodes.code]
      have hh := Nat.mod_add_div (c-n) n
      rw [Nat.mul_comm] at hh
      have hs := Nat.sub_add_cancel (Nat.le_of_not_gt hl)
      omega
  · rintro ⟨e,rfl⟩
    exact ⟨ActionCodes.code_lt Full H e,valid_code Full H e⟩

 theorem codes_eq {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n)) :
    codes (view Full H)=List.ofFn (fun i => ActionCodes.code Full H (enumeration Full H i)) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT
  · exact (ActionCodes.enumeration_strictMono Full H).sortedLT_ofFn
  · intro c
    rw [mem_codes,List.mem_ofFn]
    constructor
    · rintro ⟨e,rfl⟩
      exact ⟨(enumeration Full H).symm e,by rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨i,rfl⟩; exact ⟨enumeration Full H i,rfl⟩
end MetricKMedian.RationalBatchData.ActionList
end

end OAI
