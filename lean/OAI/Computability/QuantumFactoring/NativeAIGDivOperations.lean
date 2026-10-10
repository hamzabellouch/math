import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGDivBounded

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def divSubInput (s : DivState) : BinaryState:=
  ⟨⟨⟨s.val.base.budget,s.val.base.graph,
      shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
      s.val.base.rhs,0,(0,false),[]⟩,
    s.property.1.1,shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _),s.property.1.2.2.1,
    Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩,
    (shiftConcat_length _ _).trans (s.property.2.2.1.trans s.property.2.1)⟩
def divSubState (s : DivState) : AddState:=subState (divSubInput s)
lemma divSub_budget (s : DivState) :
    (divSubState s).val.budget=s.val.base.budget+26*s.val.base.lhs.length:=by
  rw [divSubState,subState_budget]
  change s.val.base.budget+26*(shiftConcat _ _).length=_
  rw [shiftConcat_length,s.property.2.2.1]
lemma divSub_length (s : DivState) : (divSubState s).val.output.length=s.val.base.lhs.length:=
  (subState_length _).trans ((shiftConcat_length _ _).trans s.property.2.2.1)
lemma divSub_value (s : DivState) : ((divSubState s).val.graph,(divSubState s).val.output)=
    sub s.val.base.graph
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs:=
  subState_value _
def divUltInput (s : DivState) : AddState:=
  ⟨⟨(divSubState s).val.budget,(divSubState s).val.graph,
    shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
    s.val.base.rhs,0,(0,false),[]⟩,
  (divSubState s).property.1,
  (shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _)).mono (by rw [divSub_budget];omega),
  s.property.1.2.2.1.mono (by rw [divSub_budget];omega),Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def divUltState (s : DivState) : AddState:=ultState (divUltInput s)
lemma ultState_budget (s : AddState) : (ultState s).val.budget=s.val.budget+6*s.val.lhs.length:=
  overflowState_budget (ultInput s)
lemma divUlt_budget (s : DivState) :
    (divUltState s).val.budget=s.val.base.budget+32*s.val.base.lhs.length:=by
  rw [divUltState,ultState_budget]
  change (divSubState s).val.budget+
    6*(shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))).length=_
  rw [divSub_budget,shiftConcat_length,s.property.2.2.1];omega
lemma divUlt_value (s : DivState) : ((divUltState s).val.graph,notRef (divUltState s).val.cin)=
    ult (sub s.val.base.graph
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs).1
      (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))) s.val.base.rhs:=by
  have hh:=ultState_value (divUltInput s)
  change _=ult (divSubState s).val.graph _ _ at hh
  rw [show (divSubState s).val.graph=_ from congrArg Prod.fst (divSub_value s)] at hh
  exact hh

def divQInput (s : DivState) : AddState:=
  ⟨⟨(divUltState s).val.budget,(divUltState s).val.graph,
    shiftConcat s.val.quotient (0,false),shiftConcat s.val.quotient (0,true),0,
    notRef (divUltState s).val.cin,[]⟩,
  (divUltState s).property.1,
  (shiftConcat_refs s.property.2.2.2.1 (Nat.zero_le _)).mono (by rw [divUlt_budget];omega),
  (shiftConcat_refs s.property.2.2.2.1 (Nat.zero_le _)).mono (by rw [divUlt_budget];omega),
  Nat.zero_le _,(divUltState s).property.2.2.2.2.1,Nat.zero_le _,by intro a ha;cases ha⟩
def divQState (s : DivState) : AddState:=ifVecState (divQInput s)
lemma divQ_budget (s : DivState) : (divQState s).val.budget=s.val.base.budget+35*s.val.base.lhs.length:=by
  rw [divQState,ifVecState_budget]
  change (divUltState s).val.budget+3*(shiftConcat s.val.quotient (0,false)).length=_
  rw [divUlt_budget,shiftConcat_length,s.property.2.2.2.2];omega
lemma divQ_length (s : DivState) : (divQState s).val.output.length=s.val.base.lhs.length:=
  (ifVecState_length _).trans ((shiftConcat_length _ _).trans s.property.2.2.2.2)
def divRInput (s : DivState) : AddState:=
  ⟨⟨(divQState s).val.budget,(divQState s).val.graph,
    shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)),
    (divSubState s).val.output,0,notRef (divUltState s).val.cin,[]⟩,
  (divQState s).property.1,
  (shiftConcat_refs s.property.1.2.2.2.2.2 (s.property.1.2.1.get _)).mono (by rw [divQ_budget];omega),
  (divSubState s).property.2.2.2.2.2.mono (by rw [divSub_budget,divQ_budget];omega),Nat.zero_le _,
  (divUltState s).property.2.2.2.2.1.trans (by rw [divUlt_budget,divQ_budget];omega),
  Nat.zero_le _,by intro a ha;cases ha⟩
def divRState (s : DivState) : AddState:=ifVecState (divRInput s)
lemma divR_budget (s : DivState) : (divRState s).val.budget=s.val.base.budget+38*s.val.base.lhs.length:=by
  rw [divRState,ifVecState_budget]
  change (divQState s).val.budget+3*(shiftConcat s.val.base.output _).length=_
  rw [divQ_budget,shiftConcat_length,s.property.2.2.1];omega
lemma divR_length (s : DivState) : (divRState s).val.output.length=s.val.base.lhs.length:=
  (ifVecState_length _).trans ((shiftConcat_length _ _).trans s.property.2.2.1)
lemma divQR_value (s : DivState) :
    ((divRState s).val.graph,(divQState s).val.output,(divRState s).val.output)=
      divStep s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output:=by
  have hq:=ifVecState_value (divQInput s)
  have hr:=ifVecState_value (divRInput s)
  change ((divQState s).val.graph,(divQState s).val.output)=ifVec (divUltState s).val.graph
    (notRef (divUltState s).val.cin) (shiftConcat s.val.quotient (0,false)) (shiftConcat s.val.quotient (0,true)) at hq
  change ((divRState s).val.graph,(divRState s).val.output)=ifVec (divQState s).val.graph
    (notRef (divUltState s).val.cin)
    (shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false)))
    (divSubState s).val.output at hr
  have h2:=congrArg Prod.snd (divSub_value s)
  have h3:=congrArg Prod.fst (divUlt_value s)
  have h4:=congrArg Prod.snd (divUlt_value s)
  dsimp only [Prod.fst,Prod.snd] at h2 h3 h4
  rw [h3,h4] at hq
  rw [show (divQState s).val.graph=_ from congrArg Prod.fst hq,h4,h2] at hr
  dsimp only [divStep]
  apply Prod.ext
  · exact congrArg (fun x : Graph×List Ref=>x.1) hr
  · apply Prod.ext
    · exact congrArg (fun x : Graph×List Ref=>x.2) hq
    · exact congrArg (fun x : Graph×List Ref=>x.2) hr
end ExactQuantumFactoring.NativeAIG

end



end OAI
