import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGMulWrapper
import OAI.Computability.QuantumFactoring.NativeAIGSub

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

lemma neg_bound {B : ℕ} {g : Graph} {xs : List Ref} (hg : Bounded B g) (hx : RefsBound B xs) :
    Bounded (B+13*xs.length) (neg g xs).1 ∧
    RefsBound (B+13*xs.length) (neg g xs).2 ∧ (neg g xs).2.length=xs.length := by
  simpa only [notVec_length,neg] using add_bound hg (notVec_refs hx) (oneVec_refs hx.1)
    (by rw [notVec_length,oneVec_length])
lemma sub_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) (he : lhs.length=rhs.length) :
    Bounded (B+26*lhs.length) (sub g lhs rhs).1 ∧
    RefsBound (B+26*lhs.length) (sub g lhs rhs).2 ∧ (sub g lhs rhs).2.length=lhs.length := by
  have hn:=neg_bound hg hr
  have hh:=add_bound hn.1 (hl.mono (by omega)) hn.2.1 (he.trans hn.2.2.symm)
  have hb : B+13*rhs.length+13*lhs.length=B+26*lhs.length:=by omega
  simpa only [hb,sub] using hh

def negInput (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,notVec s.val.rhs,oneVec s.val.rhs.length,
    0,(0,false),[]⟩,
  s.property.1,notVec_refs s.property.2.2.1,oneVec_refs s.property.2.2.1.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def negState (s : AddState) : AddState:=addState (negInput s)
lemma negState_value (s : AddState) : ((negState s).val.graph,(negState s).val.output)=
    neg s.val.graph s.val.rhs:=addState_value _
lemma negState_budget (s : AddState) : (negState s).val.budget=s.val.budget+13*s.val.rhs.length := by
  have hh:=addState_budget_eq (negInput s) (by dsimp only [negInput];rw [notVec_length,oneVec_length])
  simpa only [negState,negInput,notVec_length] using hh
lemma negState_length (s : AddState) : (negState s).val.output.length=s.val.rhs.length := by
  have hh:=addState_length (negInput s) (by dsimp only [negInput];rw [notVec_length,oneVec_length])
  simpa only [negState,negInput,notVec_length] using hh

def subNext (s : BinaryState) : AddState:=⟨⟨(negState s.val).val.budget,(negState s.val).val.graph,
  s.val.val.lhs,(negState s.val).val.output,0,(0,false),[]⟩,
  (negState s.val).property.1,s.val.property.2.1.mono (by dsimp only;rw [negState_budget];omega),
  (negState s.val).property.2.2.2.2.2,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def subState (s : BinaryState) : AddState:=addState (subNext s)
lemma subState_value (s : BinaryState) : ((subState s).val.graph,(subState s).val.output)=
    sub s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=addState_value (subNext s)
  change _=add (negState s.val).val.graph s.val.val.lhs (negState s.val).val.output at hh
  rw [show (negState s.val).val.graph=(neg s.val.val.graph s.val.val.rhs).1 from
    congrArg Prod.fst (negState_value s.val),show (negState s.val).val.output=(neg s.val.val.graph s.val.val.rhs).2 from
    congrArg Prod.snd (negState_value s.val)] at hh
  exact hh
lemma subState_budget (s : BinaryState) : (subState s).val.budget=s.val.val.budget+26*s.val.val.lhs.length := by
  have hh:=addState_budget_eq (subNext s) (by
    change s.val.val.lhs.length=(negState s.val).val.output.length
    rw [negState_length];exact s.property)
  change (subState s).val.budget=(negState s.val).val.budget+13*s.val.val.lhs.length at hh
  rw [hh,negState_budget,←s.property];omega
lemma subState_length (s : BinaryState) : (subState s).val.output.length=s.val.val.lhs.length:=
  addState_length (subNext s) (by
    change s.val.val.lhs.length=(negState s.val).val.output.length
    rw [negState_length];exact s.property)

end ExactQuantumFactoring.NativeAIG
end

end OAI
