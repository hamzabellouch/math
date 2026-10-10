import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGCarryProcedure
import OAI.Computability.QuantumFactoring.NativeAIGSubProcedure
import OAI.Computability.QuantumFactoring.NativeAIGDiv

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma divStep_bound {B : ℕ} {g : Graph} {lhs rhs q rem : List Ref} (wn : ℕ)
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs)
    (hq : RefsBound B q) (hm : RefsBound B rem)
    (he : lhs.length=rhs.length) (hql : q.length=lhs.length) (hml : rem.length=lhs.length) :
    Bounded (B+38*lhs.length) (divStep g lhs rhs wn q rem).1 ∧
    RefsBound (B+38*lhs.length) (divStep g lhs rhs wn q rem).2.1 ∧
    RefsBound (B+38*lhs.length) (divStep g lhs rhs wn q rem).2.2 ∧
    (divStep g lhs rhs wn q rem).2.1.length=lhs.length ∧
    (divStep g lhs rhs wn q rem).2.2.length=lhs.length := by
  let r':=shiftConcat rem ((lhs.drop (wn-1)).headD (0,false))
  let posQ:=shiftConcat q (0,false)
  let negQ:=shiftConcat q (0,true)
  have hm' : RefsBound B r':=shiftConcat_refs hm (hl.get _)
  have hpq : RefsBound B posQ:=shiftConcat_refs hq (Nat.zero_le _)
  have hnq : RefsBound B negQ:=shiftConcat_refs hq (Nat.zero_le _)
  have hrlen : r'.length=lhs.length:=(shiftConcat_length _ _).trans hml
  have hplen : posQ.length=lhs.length:=(shiftConcat_length _ _).trans hql
  have hsub:=sub_bound hg hm' hr (hrlen.trans he)
  rw [hrlen] at hsub
  have hu:=ult_bound hsub.1 (hm'.mono (by omega)) (hr.mono (by omega))
  rw [hrlen] at hu
  have ht:=ifVec_bound hu.1 (hpq.mono (by omega)) (hnq.mono (by omega)) hu.2
  rw [hplen] at ht
  have ho:=ifVec_bound ht.1 (hm'.mono (by omega)) (hsub.2.1.mono (by omega)) (hu.2.trans (by omega))
  rw [hrlen] at ho
  have hB : B+26*lhs.length+6*lhs.length+3*lhs.length+3*lhs.length=B+38*lhs.length:=by omega
  rw [hB] at ho
  exact ⟨ho.1,ht.2.1.mono (by omega),ho.2.1,ht.2.2,ho.2.2⟩

structure DivData where
  base : AddData
  quotient : List Ref

def DivOK (s : DivData) : Prop:=
  AddOK s.base ∧ s.base.lhs.length=s.base.rhs.length ∧
    s.base.output.length=s.base.lhs.length ∧ RefsBound s.base.budget s.quotient ∧
    s.quotient.length=s.base.lhs.length
abbrev DivState:={s : DivData // DivOK s}
def divDataCode (s : DivData) : List Bool:=prodCode addDataCode (listCode refCode) (s.base,s.quotient)
def divStateCode (s : DivState) : List Bool:=divDataCode s.val

def divStepData (s : DivData) : DivData:=
  let ss:=divStep s.base.graph s.base.lhs s.base.rhs s.base.curr s.quotient s.base.output
  ⟨⟨s.base.budget+38*s.base.lhs.length,ss.1,s.base.lhs,s.base.rhs,s.base.curr-1,s.base.cin,ss.2.2⟩,ss.2.1⟩
lemma divStep_ok (s : DivState) : DivOK (divStepData s.val) := by
  obtain ⟨⟨hg,hl,hr,hc,hci,ho⟩,he,hm,hq,hql⟩:=s.property
  have hh:=divStep_bound s.val.base.curr hg hl hr hq ho he hql hm
  have hb : s.val.base.budget ≤ s.val.base.budget+38*s.val.base.lhs.length:=by omega
  exact ⟨⟨hh.1,hl.mono hb,hr.mono hb,by dsimp only [divStepData];omega,hci.trans hb,hh.2.2.1⟩,
    he,hh.2.2.2.2,hh.2.1,hh.2.2.2.1⟩
def divStepState (s : DivState) : DivState:=⟨divStepData s.val,divStep_ok s⟩
lemma divStepState_budget (s : DivState) :
    (divStepState s).val.base.budget=s.val.base.budget+38*s.val.base.lhs.length:=rfl
lemma divStepState_lhs (s : DivState) : (divStepState s).val.base.lhs=s.val.base.lhs:=rfl
lemma divStepState_iterate_lhs (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.lhs=s.val.base.lhs:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih,divStepState_lhs]
lemma divStepState_iterate_budget (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.budget=s.val.base.budget+38*s.val.base.lhs.length*k:=by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,divStepState_budget,divStepState_lhs];ring
lemma divStepState_iterate_loop (s : DivState) (k : ℕ) :
    (((divStepState^[k]) s).val.base.graph,((divStepState^[k]) s).val.quotient,
      ((divStepState^[k]) s).val.base.output)=
    divLoop k s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma divStateCode_bound (s : DivState) : (divStateCode s).length≤1000*(s.val.base.budget+1)^2 := by
  have ha:=addStateCode_bound ⟨s.val.base,s.property.1⟩
  have hq:=refsCode_bound s.property.2.2.2.1
  simp only [divStateCode,divDataCode,prodCode,pairBits_length]
  change _≤_ at hq
  dsimp only [addStateCode] at ha
  nlinarith [Nat.zero_le s.val.base.budget]
lemma divBudget_le_code (s : DivState) : s.val.base.budget≤(divStateCode s).length := by
  have ha:=budget_le_code ⟨s.val.base,s.property.1⟩
  simp only [divStateCode,divDataCode,prodCode,pairBits_length]
  dsimp only [addStateCode] at ha
  omega
end ExactQuantumFactoring.NativeAIG

end



end OAI
