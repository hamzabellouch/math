import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGDivWrapper
import OAI.Computability.QuantumFactoring.NativeAIGMod

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def remainderOutInput (s : BinaryState) : AddState:=
  ⟨⟨(divLoopState s).val.base.budget,(divLoopState s).val.base.graph,
    s.val.val.lhs,(divLoopState s).val.base.output,0,(divLoopState s).val.base.cin,[]⟩,
  (divLoopState s).property.1.1,by
    have h:=(divLoopState s).property.1.2.1;rw [divLoop_lhs] at h;exact h,
  (divLoopState s).property.1.2.2.2.2.2,Nat.zero_le _,(divLoopState s).property.1.2.2.2.2.1,
  Nat.zero_le _,by intro a ha;cases ha⟩
def remainderState (s : BinaryState) : AddState:=ifVecState (remainderOutInput s)
lemma remainderState_value (s : BinaryState) : ((remainderState s).val.graph,(remainderState s).val.output)=
    remainder s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=ifVecState_value (remainderOutInput s)
  change _=ifVec (divLoopState s).val.base.graph (divLoopState s).val.base.cin
    s.val.val.lhs (divLoopState s).val.base.output at hh
  rw [divLoop_cin] at hh
  have he:=divEq_value s
  have hl:=divLoop_value s
  rw [show (divEqState s).val.graph=_ from congrArg Prod.fst he] at hl
  rw [show (divEqState s).val.cin=_ from congrArg Prod.snd he,
    show (divLoopState s).val.base.graph=_ from congrArg Prod.fst hl,
    show (divLoopState s).val.base.output=_ from congrArg (fun x=>x.2.2) hl] at hh
  exact hh
lemma remainderState_budget (s : BinaryState) : (remainderState s).val.budget=
    s.val.val.budget+9*s.val.val.lhs.length+38*s.val.val.lhs.length*s.val.val.lhs.length:=by
  rw [remainderState,ifVecState_budget]
  change (divLoopState s).val.base.budget+3*s.val.val.lhs.length=_
  rw [divLoop_budget];omega
lemma remainderState_length (s : BinaryState) : (remainderState s).val.output.length=s.val.val.lhs.length:=
  ifVecState_length _
namespace Emission
noncomputable def remainderOutInputP : Procedure binaryStateCode addStateCode remainderOutInput := by
  let b:=divBudgetP.comp divLoopStateP
  let g:=divGraphP.comp divLoopStateP
  let c:=divCinP.comp divLoopStateP
  let rem:=divRemP.comp divLoopStateP
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (rem.pair ((Procedure.constant _ Nat.bits 0).pair
    (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def remainderStateP : Procedure binaryStateCode addStateCode remainderState:=ifVecStateP.comp remainderOutInputP
noncomputable def remainderP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>remainder s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  ((stateGraphP.pair stateOutputP).comp remainderStateP).congrFun remainderState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
