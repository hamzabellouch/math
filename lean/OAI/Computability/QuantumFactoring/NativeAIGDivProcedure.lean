import Mathlib
import OAI.Computability.QuantumFactoring.EmissionFurther2
import OAI.Computability.QuantumFactoring.NativeAIGDivOperations

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def stateBudgetP : Procedure addStateCode unaryCode (fun s=>s.val.budget):=
  ((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
noncomputable def stateGraphP : Procedure addStateCode graphCode (fun s=>s.val.graph):=
  addGraphP.precompose (fun s:AddState=>s.val)
noncomputable def stateOutputP : Procedure addStateCode (listCode refCode) (fun s=>s.val.output):=
  addOutputP.precompose (fun s:AddState=>s.val)
noncomputable def stateNotCinP : Procedure addStateCode refCode (fun s=>notRef s.val.cin):=
  (notRefP.comp addCinP).precompose (fun s:AddState=>s.val)
noncomputable def divBaseP : Procedure divStateCode addDataCode (fun s=>s.val.base):=
  (first addDataCode (listCode refCode)).precompose (fun s:DivState=>(s.val.base,s.val.quotient))
noncomputable def divQuotientP : Procedure divStateCode (listCode refCode) (fun s=>s.val.quotient):=
  (second addDataCode (listCode refCode)).precompose (fun s:DivState=>(s.val.base,s.val.quotient))
noncomputable def divBudgetP : Procedure divStateCode unaryCode (fun s=>s.val.base.budget):=
  ((first unaryCode addTail1).comp addViewP).comp divBaseP
noncomputable def divGraphP : Procedure divStateCode graphCode (fun s=>s.val.base.graph):=addGraphP.comp divBaseP
noncomputable def divLhsP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.lhs):=addLhsP.comp divBaseP
noncomputable def divRhsP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.rhs):=addRhsP.comp divBaseP
noncomputable def divRemP : Procedure divStateCode (listCode refCode) (fun s=>s.val.base.output):=addOutputP.comp divBaseP
noncomputable def divCurrP : Procedure divStateCode Nat.bits (fun s=>s.val.base.curr):=addCurrP.comp divBaseP
noncomputable def divCinP : Procedure divStateCode refCode (fun s=>s.val.base.cin):=addCinP.comp divBaseP
noncomputable def divPredP : Procedure divStateCode Nat.bits (fun s=>s.val.base.curr-1):=
  binarySub.comp (divCurrP.pair (Procedure.constant _ Nat.bits 1))
noncomputable def divShiftRemP : Procedure divStateCode (listCode refCode)
    (fun s=>shiftConcat s.val.base.output ((s.val.base.lhs.drop (s.val.base.curr-1)).headD (0,false))):=
  shiftConcatP.comp (divRemP.pair ((listGet refCode (0,false)).comp (divPredP.pair divLhsP)))
noncomputable def divSubInputP : Procedure divStateCode binaryStateCode divSubInput := by
  exact (packAddP.comp (divBudgetP.pair (divGraphP.pair (divShiftRemP.pair (divRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divSubStateP : Procedure divStateCode addStateCode divSubState:=subStateP.comp divSubInputP
noncomputable def divUltInputP : Procedure divStateCode addStateCode divUltInput := by
  let b:=stateBudgetP.comp divSubStateP
  let g:=stateGraphP.comp divSubStateP
  exact (packAddP.comp (b.pair (g.pair (divShiftRemP.pair (divRhsP.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def divUltStateP : Procedure divStateCode addStateCode divUltState:=ultStateP.comp divUltInputP
noncomputable def divQInputP : Procedure divStateCode addStateCode divQInput := by
  let b:=stateBudgetP.comp divUltStateP
  let g:=stateGraphP.comp divUltStateP
  let c:=stateNotCinP.comp divUltStateP
  let q0:=shiftConcatP.comp (divQuotientP.pair (Procedure.constant _ refCode (0,false)))
  let q1:=shiftConcatP.comp (divQuotientP.pair (Procedure.constant _ refCode (0,true)))
  exact (packAddP.comp (b.pair (g.pair (q0.pair (q1.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def divQStateP : Procedure divStateCode addStateCode divQState:=ifVecStateP.comp divQInputP
noncomputable def divRInputP : Procedure divStateCode addStateCode divRInput := by
  let b:=stateBudgetP.comp divQStateP
  let g:=stateGraphP.comp divQStateP
  let c:=stateNotCinP.comp divUltStateP
  let nr:=stateOutputP.comp divSubStateP
  exact (packAddP.comp (b.pair (g.pair (divShiftRemP.pair (nr.pair
    ((Procedure.constant _ Nat.bits 0).pair (c.pair (Procedure.constant _ (listCode refCode) [])))))))).result
      (by intro s;rfl)
noncomputable def divRStateP : Procedure divStateCode addStateCode divRState:=ifVecStateP.comp divRInputP
noncomputable def divNextP : Procedure divStateCode
    (prodCode graphCode (prodCode (listCode refCode) (listCode refCode)))
    (fun s=>divStep s.val.base.graph s.val.base.lhs s.val.base.rhs s.val.base.curr s.val.quotient s.val.base.output):=
  ((stateGraphP.comp divRStateP).pair ((stateOutputP.comp divQStateP).pair
    (stateOutputP.comp divRStateP))).congrFun divQR_value
noncomputable def divStepStateP : Procedure divStateCode divStateCode divStepState := by
  let ns:=divNextP
  let g:=(first graphCode _).comp ns
  let q:=(first (listCode refCode) (listCode refCode)).comp ((second graphCode _).comp ns)
  let r:=(second (listCode refCode) (listCode refCode)).comp ((second graphCode _).comp ns)
  let len:=(listUnaryLength refCode (0,false)).comp divLhsP
  let b:=unaryAdd.comp (divBudgetP.pair (unaryMul.comp ((Procedure.constant _ unaryCode 38).pair len)))
  let base:=packAddP.comp (b.pair (g.pair (divLhsP.pair (divRhsP.pair (divPredP.pair (divCinP.pair r))))))
  exact (base.pair q).result (by intro s;rfl)
noncomputable def divIterationP : Procedure (prodCode unaryCode divStateCode) divStateCode
    (fun x=>(divStepState^[x.1]) x.2):=
  divStepStateP.iterate (Polynomial.C 1521000*(Polynomial.X+1)^4) (by
    intro n s i hi
    have hh:=divStateCode_bound ((divStepState^[i]) s)
    rw [divStepState_iterate_budget] at hh
    have hb:=divBudget_le_code s
    have hl:=s.property.1.2.1.1
    let M:=n+(divStateCode s).length+1
    have hM : 1≤M:=by dsimp [M];omega
    have hB : s.val.base.budget+1≤M:=by dsimp [M];omega
    have hw : 38*s.val.base.lhs.length≤38*M:=by omega
    have hii : i≤M:=by dsimp [M];omega
    have hm:=Nat.mul_le_mul hw hii
    have hx : s.val.base.budget+38*s.val.base.lhs.length*i+1≤39*M^2:=by nlinarith
    have hp:=Nat.pow_le_pow_left hx 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    calc
      (divStateCode ((divStepState^[i]) s)).length≤1000*(s.val.base.budget+38*s.val.base.lhs.length*i+1)^2:=hh
      _ ≤ 1000*(39*M^2)^2:=Nat.mul_le_mul_left _ hp
      _ = 1521000*(n+(divStateCode s).length+1)^4:=by dsimp [M];ring)
end ExactQuantumFactoring.NativeAIG.Emission

end


end OAI
