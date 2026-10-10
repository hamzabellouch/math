import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGEqProcedure
import OAI.Computability.QuantumFactoring.NativeAIGDivProcedure

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def divEqInput (s : BinaryState) : AddState:=
  ⟨⟨s.val.val.budget,s.val.val.graph,s.val.val.rhs,List.replicate s.val.val.lhs.length (0,false),
    0,(0,false),[]⟩,s.val.property.1,s.val.property.2.2.1,
    RefsBound.zeros s.val.property.2.1.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
def divEqState (s : BinaryState) : AddState:=eqState (divEqInput s)
lemma divEq_budget (s : BinaryState) : (divEqState s).val.budget=s.val.val.budget+6*s.val.val.lhs.length:=by
  rw [divEqState,eqState_budget]
  change s.val.val.budget+6*s.val.val.rhs.length=_
  rw [s.property]
lemma divEq_value (s : BinaryState) : ((divEqState s).val.graph,(divEqState s).val.cin)=
    eqVec s.val.val.graph s.val.val.rhs (List.replicate s.val.val.lhs.length (0,false)):=eqState_value _
def initializeDiv (s : BinaryState) : DivState:=
  ⟨⟨⟨(divEqState s).val.budget,(divEqState s).val.graph,s.val.val.lhs,s.val.val.rhs,
    s.val.val.lhs.length,(divEqState s).val.cin,List.replicate s.val.val.lhs.length (0,false)⟩,
    List.replicate s.val.val.lhs.length (0,false)⟩,
  ⟨(divEqState s).property.1,s.val.property.2.1.mono (by rw [divEq_budget];omega),
    s.val.property.2.2.1.mono (by rw [divEq_budget];omega),by
      change s.val.val.lhs.length ≤ (divEqState s).val.budget
      have h:=s.val.property.2.1.1;rw [divEq_budget];omega,
    (divEqState s).property.2.2.2.2.1,RefsBound.zeros (by
      have h:=s.val.property.2.1.1;rw [divEq_budget];omega)⟩,
  s.property,by simp,RefsBound.zeros (by have h:=s.val.property.2.1.1;rw [divEq_budget];omega),by simp⟩
def divLoopState (s : BinaryState) : DivState:=(divStepState^[s.val.val.lhs.length]) (initializeDiv s)
lemma divStepState_iterate_cin (s : DivState) (k : ℕ) :
    ((divStepState^[k]) s).val.base.cin=s.val.base.cin:=by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl
lemma divLoop_budget (s : BinaryState) : (divLoopState s).val.base.budget=
    s.val.val.budget+6*s.val.val.lhs.length+38*s.val.val.lhs.length*s.val.val.lhs.length:=by
  rw [divLoopState,divStepState_iterate_budget]
  change (divEqState s).val.budget+38*s.val.val.lhs.length*s.val.val.lhs.length=_
  rw [divEq_budget]
lemma divLoop_lhs (s : BinaryState) : (divLoopState s).val.base.lhs=s.val.val.lhs:=
  divStepState_iterate_lhs _ _
lemma divLoop_cin (s : BinaryState) : (divLoopState s).val.base.cin=(divEqState s).val.cin:=
  divStepState_iterate_cin _ _
lemma divLoop_value (s : BinaryState) :
    ((divLoopState s).val.base.graph,(divLoopState s).val.quotient,(divLoopState s).val.base.output)=
    divLoop s.val.val.lhs.length (divEqState s).val.graph s.val.val.lhs s.val.val.rhs s.val.val.lhs.length
      (List.replicate s.val.val.lhs.length (0,false)) (List.replicate s.val.val.lhs.length (0,false)):=
  divStepState_iterate_loop _ _
def divideOutInput (s : BinaryState) : AddState:=
  ⟨⟨(divLoopState s).val.base.budget,(divLoopState s).val.base.graph,
    List.replicate s.val.val.lhs.length (0,false),(divLoopState s).val.quotient,0,
    (divLoopState s).val.base.cin,[]⟩,
  (divLoopState s).property.1.1,RefsBound.zeros (by
    have h:=(divLoopState s).property.1.2.1.1;rw [divLoop_lhs] at h;exact h),
  (divLoopState s).property.2.2.2.1,Nat.zero_le _,(divLoopState s).property.1.2.2.2.2.1,
  Nat.zero_le _,by intro a ha;cases ha⟩
def divideState (s : BinaryState) : AddState:=ifVecState (divideOutInput s)
lemma divideState_value (s : BinaryState) : ((divideState s).val.graph,(divideState s).val.output)=
    divide s.val.val.graph s.val.val.lhs s.val.val.rhs := by
  have hh:=ifVecState_value (divideOutInput s)
  change _=ifVec (divLoopState s).val.base.graph (divLoopState s).val.base.cin
    (List.replicate s.val.val.lhs.length (0,false)) (divLoopState s).val.quotient at hh
  rw [divLoop_cin] at hh
  have he:=divEq_value s
  have hl:=divLoop_value s
  rw [show (divEqState s).val.graph=_ from congrArg Prod.fst he] at hl
  rw [show (divEqState s).val.cin=_ from congrArg Prod.snd he,
    show (divLoopState s).val.base.graph=_ from congrArg Prod.fst hl,
    show (divLoopState s).val.quotient=_ from congrArg (fun x=>x.2.1) hl] at hh
  exact hh
lemma divideState_budget (s : BinaryState) : (divideState s).val.budget=
    s.val.val.budget+9*s.val.val.lhs.length+38*s.val.val.lhs.length*s.val.val.lhs.length:=by
  rw [divideState,ifVecState_budget]
  change (divLoopState s).val.base.budget+3*(List.replicate s.val.val.lhs.length (0,false)).length=_
  rw [divLoop_budget,List.length_replicate];omega
lemma divideState_length (s : BinaryState) : (divideState s).val.output.length=s.val.val.lhs.length:=
  (ifVecState_length _).trans (List.length_replicate ..)

namespace Emission
noncomputable def divEqInputP : Procedure binaryStateCode addStateCode divEqInput := by
  let b:=stateBudgetP.precompose (fun s:BinaryState=>s.val)
  exact (packAddP.comp (b.pair (binaryGraphP.pair (binaryRhsP.pair ((zerosP.comp binaryLhsP).pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divEqStateP : Procedure binaryStateCode addStateCode divEqState:=eqStateP.comp divEqInputP
noncomputable def initializeDivP : Procedure binaryStateCode divStateCode initializeDiv := by
  let b:=stateBudgetP.comp divEqStateP
  let g:=stateGraphP.comp divEqStateP
  let c:=(addCinP.precompose (fun s:AddState=>s.val)).comp divEqStateP
  let len:=(listLength refCode (0,false)).comp binaryLhsP
  let zs:=zerosP.comp binaryLhsP
  let s:=packAddP.comp (b.pair (g.pair (binaryLhsP.pair (binaryRhsP.pair (len.pair (c.pair zs))))))
  exact (s.pair zs).result (by intro s;rfl)
noncomputable def divLoopStateP : Procedure binaryStateCode divStateCode divLoopState:=
  divIterationP.comp (((listUnaryLength refCode (0,false)).comp binaryLhsP).pair initializeDivP)
noncomputable def divideOutInputP : Procedure binaryStateCode addStateCode divideOutInput := by
  let b:=divBudgetP.comp divLoopStateP
  let g:=divGraphP.comp divLoopStateP
  let c:=divCinP.comp divLoopStateP
  let q:=divQuotientP.comp divLoopStateP
  let zs:=zerosP.comp binaryLhsP
  exact (packAddP.comp (b.pair (g.pair (zs.pair (q.pair ((Procedure.constant _ Nat.bits 0).pair
    (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divideStateP : Procedure binaryStateCode addStateCode divideState:=ifVecStateP.comp divideOutInputP
noncomputable def divideP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>divide s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  ((stateGraphP.pair stateOutputP).comp divideStateP).congrFun divideState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
