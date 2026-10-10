import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper
import OAI.Computability.QuantumFactoring.NativeAIGIf

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
lemma RefsBound.push_inc {B c : ℕ} {xs : List Ref} (hx : RefsBound B xs)
    (hc : 1 ≤ c) (a : Ref) (ha : a.1 ≤ B+c) : RefsBound (B+c) (xs++[a]) := by
  refine ⟨?_,?_⟩
  · simp only [List.length_append,List.length_singleton];have:=hx.1;omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hx.2 r hr).trans (by omega)
    · have he : r=a:=List.mem_singleton.mp hr
      simpa only [he] using ha

def ifStepData (s : AddData) : AddData :=
  let r:=ifGate s.graph s.cin ((s.lhs.drop s.curr).headD (0,false)) ((s.rhs.drop s.curr).headD (0,false))
  ⟨s.budget+3,r.1,s.lhs,s.rhs,s.curr+1,s.cin,s.output++[r.2]⟩
lemma ifStep_ok (s : AddState) : AddOK (ifStepData s.val) := by
  obtain ⟨hg,hl,hr,hc,hci,ho⟩:=s.property
  have hh:=ifGate_bound hg s.val.cin _ _ hci (hl.get s.val.curr) (hr.get s.val.curr)
  unfold AddOK
  dsimp only [ifStepData]
  exact ⟨hh.1,hl.mono (by omega),hr.mono (by omega),by omega,by omega,
    ho.push_inc (by omega) _ hh.2⟩
def ifStep (s : AddState) : AddState:=⟨ifStepData s.val,ifStep_ok s⟩
lemma ifStep_budget (s : AddState) : (ifStep s).val.budget=s.val.budget+3 := rfl
lemma ifStep_iterate_budget (s : AddState) (k : ℕ) :
    ((ifStep^[k]) s).val.budget=s.val.budget+3*k := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>rw [Function.iterate_succ_apply,ih,ifStep_budget];omega
lemma ifStep_iterate_loop (s : AddState) (k : ℕ) :
    (((ifStep^[k]) s).val.graph,((ifStep^[k]) s).val.output)=
      ifLoop k s.val.graph s.val.cin s.val.lhs s.val.rhs s.val.curr s.val.output := by
  induction k generalizing s with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply,ih];rfl

def initializeIfData (s : AddData) : AddData:=⟨s.budget,s.graph,s.lhs,s.rhs,0,s.cin,[]⟩
lemma initializeIf_ok (s : AddState) : AddOK (initializeIfData s.val) := by
  exact ⟨s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,s.property.2.2.2.2.1,
    ⟨Nat.zero_le _,by intro a ha;cases ha⟩⟩
def initializeIf (s : AddState) : AddState:=⟨initializeIfData s.val,initializeIf_ok s⟩
def ifVecState (s : AddState) : AddState:=(ifStep^[s.val.lhs.length]) (initializeIf s)
lemma ifVecState_value (s : AddState) :
    ((ifVecState s).val.graph,(ifVecState s).val.output)=ifVec s.val.graph s.val.cin s.val.lhs s.val.rhs :=
  ifStep_iterate_loop (initializeIf s) s.val.lhs.length
lemma ifVecState_budget (s : AddState) :
    (ifVecState s).val.budget=s.val.budget+3*s.val.lhs.length :=
  ifStep_iterate_budget (initializeIf s) s.val.lhs.length
namespace Emission
noncomputable def ifStepDataP : Procedure addDataCode addDataCode ifStepData := by
  let budget:=(first unaryCode addTail1).comp addViewP
  let newBudget:=unaryAdd.comp (budget.pair (Procedure.constant _ unaryCode 3))
  let lhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=ifP.comp (addGraphP.pair (addCinP.pair (lhsBit.pair rhsBit)))
  let g:=(first graphCode refCode).comp s
  let outBit:=(second graphCode refCode).comp s
  let out:=(listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp outBit))
  exact (packAddP.comp (newBudget.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (addCinP.pair out))))))).congrFun (by intro s;rfl)
noncomputable def ifStepP : Procedure addStateCode addStateCode ifStep :=
  (ifStepDataP.precompose Subtype.val).result (by intro s;rfl)
noncomputable def ifIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(ifStep^[x.1]) x.2) :=
  ifStepP.iterate (Polynomial.C 2700*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((ifStep^[i]) s)
    rw [ifStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hb' : s.val.budget+3*i+1 ≤ 3*(n+(addStateCode s).length+1):=by omega
    have hs:=Nat.pow_le_pow_left hb' 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def initializeIfDataP : Procedure addDataCode addDataCode initializeIfData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addLhsP.pair (addRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair (addCinP.pair
      (Procedure.constant _ (listCode refCode) [])))))))).congrFun (by intro x;rfl)
noncomputable def initializeIfP : Procedure addStateCode addStateCode initializeIf :=
  (initializeIfDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def ifVecStateP : Procedure addStateCode addStateCode ifVecState :=
  ifIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeIfP)
noncomputable def ifVecP : Procedure addStateCode (prodCode graphCode (listCode refCode))
    (fun s=>ifVec s.val.graph s.val.cin s.val.lhs s.val.rhs) :=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp ifVecStateP).congrFun ifVecState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
