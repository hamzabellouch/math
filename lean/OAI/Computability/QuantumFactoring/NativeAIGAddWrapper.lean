import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGAddProcedure
import OAI.Computability.QuantumFactoring.NativeAIGKnownProcedure

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def initializeAddData (s : AddData) : AddData:=⟨s.budget,s.graph,s.lhs,s.rhs,0,(0,false),[]⟩
lemma initializeAdd_ok (s : AddState) : AddOK (initializeAddData s.val) := by
  exact ⟨s.property.1,s.property.2.1,s.property.2.2.1,Nat.zero_le _,Nat.zero_le _,
    ⟨Nat.zero_le _,by intro a ha;cases ha⟩⟩
def initializeAdd (s : AddState) : AddState:=⟨initializeAddData s.val,initializeAdd_ok s⟩
def swapAddData (s : AddData) : AddData:=⟨s.budget,s.graph,s.rhs,s.lhs,s.curr,s.cin,s.output⟩
def swapAdd (s : AddState) : AddState:=⟨swapAddData s.val,
  ⟨s.property.1,s.property.2.2.1,s.property.2.1,s.property.2.2.2⟩⟩
def addBlastState (s : AddState) : AddState:=(addStep^[s.val.lhs.length]) (initializeAdd s)
def addState (s : AddState) : AddState:=
  if countKnown s.val.graph s.val.lhs<countKnown s.val.graph s.val.rhs then
    addBlastState s else addBlastState (swapAdd s)
lemma addBlastState_value (s : AddState) :
    ((addBlastState s).val.graph,(addBlastState s).val.output)=addBlast s.val.graph s.val.lhs s.val.rhs :=
  addStep_iterate_loop (initializeAdd s) s.val.lhs.length
lemma addState_value (s : AddState) :
    ((addState s).val.graph,(addState s).val.output)=add s.val.graph s.val.lhs s.val.rhs := by
  unfold addState add
  split <;> exact addBlastState_value _
lemma addBlastState_budget (s : AddState) :
    (addBlastState s).val.budget=s.val.budget+13*s.val.lhs.length :=
  addStep_iterate_budget (initializeAdd s) s.val.lhs.length
lemma addState_budget (s : AddState) : (addState s).val.budget≤14*s.val.budget := by
  unfold addState
  split
  · rw [addBlastState_budget];have:=s.property.2.1.1;omega
  · rw [addBlastState_budget];change s.val.budget+13*s.val.rhs.length≤_
    have:=s.property.2.2.1.1;omega

namespace Emission
noncomputable def listUnaryLength {α : Type} (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) unaryCode List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (Procedure.constant (listCode ea) unaryCode 0)
  exact (rep.comp start).congrFun (by
    intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
noncomputable def initializeAddDataP : Procedure addDataCode addDataCode initializeAddData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addLhsP.pair (addRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).congrFun (by intro x;rfl)
noncomputable def initializeAddP : Procedure addStateCode addStateCode initializeAdd :=
  (initializeAddDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def swapAddDataP : Procedure addDataCode addDataCode swapAddData := by
  let b:=(first unaryCode addTail1).comp addViewP
  exact (packAddP.comp (b.pair (addGraphP.pair (addRhsP.pair
    (addLhsP.pair (addCurrP.pair (addCinP.pair addOutputP))))))).congrFun (by intro x;rfl)
noncomputable def swapAddP : Procedure addStateCode addStateCode swapAdd :=
  (swapAddDataP.precompose (fun s:AddState=>s.val)).result (by intro s;rfl)
noncomputable def addBlastStateP : Procedure addStateCode addStateCode addBlastState :=
  addIterationP.comp (((listUnaryLength refCode (0,false)).comp
    (addLhsP.precompose (fun s:AddState=>s.val))).pair initializeAddP)
noncomputable def addStateP : Procedure addStateCode addStateCode addState := by
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let lhs:=addLhsP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  let lk:=countKnownP.comp (g.pair lhs)
  let rk:=countKnownP.comp (g.pair rhs)
  let test:=binaryLt.comp (lk.pair rk)
  exact (conditional test addBlastStateP (addBlastStateP.comp swapAddP)).congrFun (by
    intro s;unfold addState
    split <;> simp_all)
noncomputable def addP : Procedure addStateCode (prodCode graphCode (listCode refCode))
    (fun s=>add s.val.graph s.val.lhs s.val.rhs) :=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp addStateP).congrFun addState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
