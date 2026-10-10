import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGSubProcedure

namespace OAI

section
namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def oneVecP : Procedure unaryCode (listCode refCode) oneVec := by
  let oneBit:=(Procedure.constant (prodCode unaryCode boolCode) Nat.bits 0).pair
    (unaryZero.comp (first unaryCode boolCode))
  exact ((tabulate (f:=fun (_ : Bool) i => (0,decide (i=0))) (0,false) oneBit).comp
    ((identity unaryCode).pair (Procedure.constant unaryCode boolCode false))).congrFun (by intro w;rfl)
noncomputable def negInputP : Procedure addStateCode addStateCode negInput := by
  let b:=((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)
  let g:=addGraphP.precompose (fun s:AddState=>s.val)
  let rhs:=addRhsP.precompose (fun s:AddState=>s.val)
  let one:=oneVecP.comp ((listUnaryLength refCode (0,false)).comp rhs)
  exact (packAddP.comp (b.pair (g.pair ((notVecP.comp rhs).pair (one.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def negStateP : Procedure addStateCode addStateCode negState:=addStateP.comp negInputP
noncomputable def subNextP : Procedure binaryStateCode addStateCode subNext := by
  let ns:=negStateP.precompose (fun s:BinaryState=>s.val)
  let b:=(((first unaryCode addTail1).comp addViewP).precompose (fun s:AddState=>s.val)).comp ns
  let g:=(addGraphP.precompose (fun s:AddState=>s.val)).comp ns
  let rhs:=(addOutputP.precompose (fun s:AddState=>s.val)).comp ns
  exact (packAddP.comp (b.pair (g.pair (binaryLhsP.pair (rhs.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro s;rfl)
noncomputable def subStateP : Procedure binaryStateCode addStateCode subState:=addStateP.comp subNextP
noncomputable def subP : Procedure binaryStateCode (prodCode graphCode (listCode refCode))
    (fun s=>sub s.val.val.graph s.val.val.lhs s.val.val.rhs):=
  (((addGraphP.pair addOutputP).precompose (fun s:AddState=>s.val)).comp subStateP).congrFun subState_value
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
