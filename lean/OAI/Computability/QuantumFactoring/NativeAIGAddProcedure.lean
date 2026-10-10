import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGAddBounded
import OAI.Computability.QuantumFactoring.Emission

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
namespace Emission
abbrev addTail5 := prodCode refCode (listCode refCode)
abbrev addTail4 := prodCode Nat.bits addTail5
abbrev addTail3 := prodCode (listCode refCode) addTail4
abbrev addTail2 := prodCode (listCode refCode) addTail3
abbrev addTail1 := prodCode graphCode addTail2
abbrev addPayload := prodCode unaryCode addTail1
noncomputable def addViewP : Procedure addDataCode addPayload addDataView :=
  ((identity addPayload).precompose addDataView)
noncomputable def packAddP : Procedure addPayload addDataCode
    (fun x=>AddData.mk x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2) :=
  (identity addPayload).result (by intro x;rfl)
noncomputable def addGraphP : Procedure addDataCode graphCode AddData.graph :=
  (first graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)
noncomputable def addLhsP : Procedure addDataCode (listCode refCode) AddData.lhs :=
  (first (listCode refCode) addTail3).comp ((second graphCode addTail2).comp
    ((second unaryCode addTail1).comp addViewP))
noncomputable def addRhsP : Procedure addDataCode (listCode refCode) AddData.rhs :=
  (first (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
    ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))
noncomputable def addCurrP : Procedure addDataCode Nat.bits AddData.curr :=
  (first Nat.bits addTail5).comp ((second (listCode refCode) addTail4).comp
    ((second (listCode refCode) addTail3).comp ((second graphCode addTail2).comp
      ((second unaryCode addTail1).comp addViewP))))
noncomputable def addCinP : Procedure addDataCode refCode AddData.cin :=
  (first refCode (listCode refCode)).comp ((second Nat.bits addTail5).comp
    ((second (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
      ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))))
noncomputable def addOutputP : Procedure addDataCode (listCode refCode) AddData.output :=
  (second refCode (listCode refCode)).comp ((second Nat.bits addTail5).comp
    ((second (listCode refCode) addTail4).comp ((second (listCode refCode) addTail3).comp
      ((second graphCode addTail2).comp ((second unaryCode addTail1).comp addViewP)))))
noncomputable def addStepDataP : Procedure addDataCode addDataCode addStepData := by
  let budget:=(first unaryCode addTail1).comp addViewP
  let newBudget:=unaryAdd.comp (budget.pair (Procedure.constant _ unaryCode 13))
  let lhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addLhsP)
  let rhsBit:=(listGet refCode (0,false)).comp (addCurrP.pair addRhsP)
  let s:=fullP.comp (addGraphP.pair (lhsBit.pair (rhsBit.pair addCinP)))
  let g:=(first graphCode keyCode).comp s
  let refs:=(second graphCode keyCode).comp s
  let outBit:=(first refCode refCode).comp refs
  let cin:=(second refCode refCode).comp refs
  let out:=(listAppend refCode (0,false)).comp (addOutputP.pair ((singleton refCode).comp outBit))
  exact (packAddP.comp (newBudget.pair (g.pair (addLhsP.pair (addRhsP.pair
    ((successor.comp addCurrP).pair (cin.pair out))))))).congrFun (by intro s;rfl)
noncomputable def addStepP : Procedure addStateCode addStateCode addStep :=
  (addStepDataP.precompose Subtype.val).result (by intro s;rfl)
noncomputable def addIterationP : Procedure (prodCode unaryCode addStateCode) addStateCode
    (fun x=>(addStep^[x.1]) x.2) :=
  addStepP.iterate (Polynomial.C 50700*(Polynomial.X+1)^2) (by
    intro n s i hi
    have hh:=addStateCode_bound ((addStep^[i]) s)
    rw [addStep_iterate_budget] at hh
    have hb:=budget_le_code s
    have hb' : s.val.budget+13*i+1≤13*(n+(addStateCode s).length+1):=by omega
    have hs:=Nat.pow_le_pow_left hb' 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith)
noncomputable def addLoopP : Procedure (prodCode unaryCode addStateCode)
    (prodCode graphCode (listCode refCode))
    (fun x=>addLoop x.1 x.2.val.graph x.2.val.lhs x.2.val.rhs x.2.val.curr x.2.val.cin x.2.val.output) :=
  (((addGraphP.pair addOutputP).precompose Subtype.val).comp addIterationP).congrFun
    (fun x=>addStep_iterate_loop x.2 x.1)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
