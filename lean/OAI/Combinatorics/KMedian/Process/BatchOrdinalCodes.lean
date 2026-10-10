import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchActionList
import OAI.Combinatorics.KMedian.Binary.BinaryAutoFiniteLists

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

abbrev pairOrder : LinearOrder (I × I) :=
  LinearOrder.lift' (fun p : I × I => toLex p) (fun _ _ h => h)
abbrev actionOrder : LinearOrder (HeavyAction D H) := by
  letI : LinearOrder (I × I) := pairOrder (I:=I)
  exact LinearOrder.lift' (fun e : HeavyAction D H => toLex e) (fun _ _ h => h)

def code : HeavyAction D H → ℕ
 | .inl h => (r.symm h.val).val
 | .inr p => n+(r.symm p.val.1).val*n+(r.symm p.val.2).val

def sets (S : Finset I) : Row := setView (S.map r.symm.toEquiv.toEmbedding)
def view : ActionList.Raw := (List.ofFn fun h => sets r (D.erase (r h)),sets r H)

 theorem sets_eq (S : Finset I) : sets r S=List.ofFn (fun i => decide (r i∈S)) := by
  simp only [sets,setView,mem_map_equiv]
  rfl
 theorem sets_length (S : Finset I) : (sets r S).length=n := by rw [sets_eq,List.length_ofFn]
 theorem sets_card (S : Finset I) : ((sets r S).filter id).length=S.card := by
  exact (MetricKMedian.EncodingLists.bool_card _).trans (card_map _)

 theorem code_strictMono : @StrictMono _ _ (actionOrder D H).toPreorder _ (code r D H) := by
  let : LinearOrder (I × I) := pairOrder (I:=I)
  let : LinearOrder (HeavyAction D H) := actionOrder D H
  intro e f hef
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hh := Sum.lex_inl_inl.mp hef
      exact r.symm.strictMono hh
    | inr f =>
      simp only [code]
      have he := (r.symm e.val).isLt
      omega
  | inr e =>
    cases f with
    | inl f => cases hef
    | inr f =>
      have hh := Sum.lex_inr_inr.mp hef
      change Prod.Lex (fun a b : I => a<b) (fun a b : I => a<b) e.val f.val at hh
      rcases Prod.lex_def.mp hh with h | ⟨h,h'⟩
      · have h1 : (r.symm e.val.1).val+1≤(r.symm f.val.1).val := r.symm.strictMono h
        have h2 := (r.symm e.val.2).isLt
        simp only [code]
        nlinarith
      · have h1 := congrArg (fun i => (r.symm i).val) h
        have h2 : (r.symm e.val.2).val<(r.symm f.val.2).val := r.symm.strictMono h'
        simp only [code]
        rw [h1]
        omega
 theorem code_lt (e : HeavyAction D H) : code r D H e<n+n*n := by
  cases e with
  | inl e => simp only [code]; have he := (r.symm e.val).isLt; omega
  | inr e =>
    simp only [code]
    have he := (r.symm e.val.1).isLt
    have hf := (r.symm e.val.2).isLt
    nlinarith
 theorem enumeration_strictMono [Fintype I] : StrictMono (fun i => code r D H (enumeration D H i)) := by
  let : LinearOrder (I × I) := pairOrder (I:=I)
  let : LinearOrder (HeavyAction D H) := actionOrder D H
  intro i j hij
  apply code_strictMono r D H
  exact @OrderIso.strictMono _ _ _ (actionOrder D H).toPreorder
    (@Fintype.orderIsoFinOfCardEq (HeavyAction D H) (actionOrder D H) _ _ rfl) i j hij
 theorem code_light (e : HeavyAction D H) : code r D H e<n ↔ e.isLeft=true := by
  cases e with
  | inl e => simp only [code,Fin.isLt,Sum.isLeft_inl]
  | inr e => simp only [code,Sum.isLeft_inr,Bool.false_eq_true,iff_false]; omega
 theorem parent_code (e : HeavyAction D H) :
    ActionList.parent n (code r D H e)=(r.symm (heavyParent D H e)).val := by
  cases e with
  | inl e => simp only [ActionList.parent,code,Fin.isLt,ite_true,heavyParent]
  | inr e =>
    have hn : 0<n := Nat.zero_lt_of_lt (r.symm e.val.1).isLt
    have hi := (r.symm e.val.2).isLt
    have hc : ¬n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionList.parent n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.1).val
    rw [ActionList.parent,ite_eq_right hc,Nat.add_assoc,Nat.add_sub_cancel_left,Nat.mul_comm _ n,
      Nat.mul_add_div hn,Nat.div_eq_of_lt hi,Nat.add_zero]
 theorem child_code (e : {p : I × I // p.1∈H ∧ p.2∈D.erase p.1}) :
    ActionList.child n (code r D H (.inr e))=(r.symm e.val.2).val := by
  simp only [ActionList.child,code]
  rw [Nat.add_assoc,Nat.add_sub_cancel_left,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (r.symm e.val.2).isLt]
 theorem valid_code (e : HeavyAction D H) : ActionList.valid (view r D H) (code r D H e)=true := by
  have hp := parent_code r D H e
  cases e with
  | inl e =>
    change ActionList.valid (view r D H) (r.symm e.val).val=true
    simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ite_eq_left (r.symm e.val).isLt,
      List.getElem?_ofFn,dite_eq_left (r.symm e.val).isLt,Option.getD_some,Fin.eta,
      OrderIso.apply_symm_apply,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not]
    exact e.property
  | inr e =>
    have hc : ¬n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionList.valid (view r D H) (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=true
    simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ite_eq_right hc]
    rw [show ActionList.parent n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.1).val from hp,
      show ActionList.child n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.2).val from child_code r D H e]
    simp only [List.getElem?_ofFn,dite_eq_left (r.symm e.val.1).isLt,dite_eq_left (r.symm e.val.2).isLt,
      Option.getD_some,Fin.eta,OrderIso.apply_symm_apply,decide_eq_true e.property.1,decide_eq_true e.property.2,Bool.and_self]
 theorem units_length : (ActionList.units (view r D H)).length=n+n*n := by
  simp [ActionList.units,view,sets_eq,List.length_flatMap,Function.comp_def]
 theorem mem_codes (c : ℕ) : c∈ActionList.codes (view r D H) ↔ ∃ e, code r D H e=c := by
  simp only [ActionList.codes,indices,units_length,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨hc,hv⟩
    by_cases hl : c<n
    · simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ite_eq_left hl,List.getElem?_ofFn,dite_eq_left hl,
        Option.getD_some,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not] at hv
      refine ⟨.inl ⟨r ⟨c,hl⟩,hv⟩,?_⟩
      simp only [code,OrderIso.symm_apply_apply]
    · have hn : 0<n := by nlinarith
      have hq : (c-n)/n<n := (Nat.div_lt_iff_lt_mul hn).mpr (by omega)
      have hr : (c-n)%n<n := Nat.mod_lt _ hn
      simp only [ActionList.valid,view,sets_eq,List.length_ofFn,ActionList.parent,ite_eq_right hl,ActionList.child,
        List.getElem?_ofFn,dite_eq_left hq,dite_eq_left hr,Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at hv
      refine ⟨.inr ⟨(r ⟨(c-n)/n,hq⟩,r ⟨(c-n)%n,hr⟩),hv⟩,?_⟩
      simp only [code,OrderIso.symm_apply_apply]
      have hh := Nat.mod_add_div (c-n) n
      rw [Nat.mul_comm] at hh
      have hs := Nat.sub_add_cancel (Nat.le_of_not_gt hl)
      omega
  · rintro ⟨e,rfl⟩; exact ⟨code_lt r D H e,valid_code r D H e⟩
 theorem codes_eq [Fintype I] : ActionList.codes (view r D H)=List.ofFn (fun i => code r D H (enumeration D H i)) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT
  · exact (enumeration_strictMono r D H).sortedLT_ofFn
  · intro c
    rw [mem_codes,List.mem_ofFn]
    constructor
    · rintro ⟨e,rfl⟩; exact ⟨(enumeration D H).symm e,by rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨i,rfl⟩; exact ⟨enumeration D H i,rfl⟩
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
