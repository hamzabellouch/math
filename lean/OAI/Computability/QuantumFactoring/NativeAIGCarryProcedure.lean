import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGIfProcedure
import OAI.Computability.QuantumFactoring.NativeAIGCarry

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def carryStepData (s : AddData) : AddData:=
  let next:=fullCarry s.graph ((s.lhs.drop s.curr).headD (0,false))
    ((s.rhs.drop s.curr).headD (0,false)) s.cin
  ⟨s.budget+6,next.1,s.lhs,s.rhs,s.curr+1,next.2,s.output⟩
lemma carryStep_ok (s : AddState) : AddOK (carryStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=fullCarry_bound hg _ _ s.val.cin (hl.get s.val.curr) (hr.get s.val.curr) hci
  dsimp only [AddOK,carryStepData]
  exact ⟨hh.1,hl.mono (by omega),hr.mono (by omega),by omega,hh.2,ho.mono (by omega)⟩
def carryStep (s : AddState) : AddState:=⟨carryStepData s.val,carryStep_ok s⟩
lemma carryStep_budget (s : AddState) : (carryStep s).val.budget=s.val.budget+6:=rfl
lemma carryStep_iterate_budget (s : AddState) (k : ℕ) :
    ((carryStep^[k]) s).val.budget=s.val.budget+6*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,carryStep_budget];omega
lemma carryStep_iterate_loop (s : AddState) (k : ℕ) :
    (((carryStep^[k]) s).val.graph,((carryStep^[k]) s).val.cin)=
      carryLoop k s.val.graph s.val.lhs s.val.rhs s.val.curr s.val.cin := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl

def overflowState (s : AddState) : AddState:=(carryStep^[s.val.lhs.length]) (initializeIf s)
lemma overflowState_value (s : AddState) : ((overflowState s).val.graph,(overflowState s).val.cin)=
    overflow s.val.graph s.val.lhs s.val.rhs s.val.cin:=carryStep_iterate_loop _ _
lemma overflowState_budget (s : AddState) : (overflowState s).val.budget=s.val.budget+6*s.val.lhs.length:=
  carryStep_iterate_budget _ _
def ultInput (s : AddState) : AddState:=⟨⟨s.val.budget,s.val.graph,s.val.lhs,notVec s.val.rhs,0,(0,true),[]⟩,
  s.property.1,s.property.2.1,notVec_refs s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,
  by intro a ha;cases ha⟩
def ultState (s : AddState) : AddState:=overflowState (ultInput s)
lemma ultState_value (s : AddState) : ((ultState s).val.graph,notRef (ultState s).val.cin)=
    ult s.val.graph s.val.lhs s.val.rhs :=by
  have hh:=overflowState_value (ultInput s)
  exact congrArg (fun x : Graph×Ref=>(x.1,notRef x.2)) hh
lemma ult_bound {B : ℕ} {g : Graph} {lhs rhs : List Ref}
    (hg : Bounded B g) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+6*lhs.length) (ult g lhs rhs).1 ∧ (ult g lhs rhs).2.1≤B+6*lhs.length := by
  let s : AddState:=⟨⟨B,g,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hh:=(ultState s).property
  have hb:=overflowState_budget (ultInput s)
  rw [←ultState_value s]
  change Bounded (B+6*lhs.length) (ultState s).val.graph ∧ (ultState s).val.cin.1≤B+6*lhs.length
  change (ultState s).val.budget=B+6*lhs.length at hb
  rw [←hb]
  exact ⟨hh.1,hh.2.2.2.2.1⟩
namespace Emission
noncomputable def carryStepDataP : Procedure addDataCode addDataCode carryStepData := by
  let b:=unaryAdd.comp (((first unaryCode addTail1).comp addViewP).pair (Procedure.constant _ unaryCode 6))
  let lhs:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhs:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=fullCarryP.comp (addGraphP.pair (lhs.pair (rhs.pair addCinP)))
  let g:=(first graphCode refCode).comp s
  let c:=(second graphCode refCode).comp s
  exact (packAddP.comp (b.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (c.pair addOutputP))))))).congrFun (by intro s;rfl)
noncomputable def carryStepP : Procedure addStateCode addStateCode carryStep:=
  (carryStepDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def carryIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(carryStep^[x.1]) x.2):=
  carryStepP.iterate (Polynomial.C 10800*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((carryStep^[i]) s)
    rw [carryStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have h : s.val.budget+6*i+1 ≤ 6*(n+(addStateCode s).length+1):=by omega
    have hp:=Nat.pow_le_pow_left h 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def overflowStateP : Procedure addStateCode addStateCode overflowState:=
  carryIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeIfP)
noncomputable def ultInputP : Procedure addStateCode addStateCode ultInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=notVecP.comp (addRhsP.precompose (fun s:AddState=>s.val))
  exact (packAddP.comp (b.pair (g.pair (lhs.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,true)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def ultStateP : Procedure addStateCode addStateCode ultState:=overflowStateP.comp ultInputP
noncomputable def ultP : Procedure addStateCode (prodCode graphCode refCode)
    (fun s=>ult s.val.graph s.val.lhs s.val.rhs) :=
  ((((addGraphP.pair (notRefP.comp addCinP)).precompose (fun s:AddState=>s.val)).comp ultStateP)).congrFun
    ultState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
