import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListMapWith
import OAI.Computability.QuantumFactoring.BitStackListWords
import OAI.Computability.QuantumFactoring.CircuitEmissionModel
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def natWordP : Procedure unaryCode id natWord :=
  ((append.comp ((identity (id : List Bool→List Bool)).pair
    (Procedure.constant (id : List Bool→List Bool) id [false]))).precompose unaryCode).congrFun (by intro n;rfl)
noncomputable def gateViewP : Procedure gateCode gatePayload gateView:=
  (identity gatePayload).precompose gateView
noncomputable def gatePrimitiveP : Procedure gateCode primitiveCode Gate.primitive:=
  (first primitiveCode _).comp gateViewP
noncomputable def gateInverseP : Procedure gateCode boolCode Gate.inverse:=
  (first boolCode boolCode).comp ((second primitiveCode _).comp gateViewP)
noncomputable def gateControlledP : Procedure gateCode boolCode Gate.controlled:=
  (second boolCode boolCode).comp ((second primitiveCode _).comp gateViewP)
noncomputable def gateHeaderP : Procedure gateCode id
    (fun g=>natWord g.primitive.code++[g.inverse,g.controlled]) := by
  let primitiveWord:=(natWordP.precompose Primitive.code).comp gatePrimitiveP
  let c:=cons.comp (gateControlledP.pair (Procedure.constant gateCode id []))
  let tail:=cons.comp (gateInverseP.pair c)
  exact (append.comp (primitiveWord.pair tail)).congrFun (by intro g;rfl)
noncomputable def opViewP : Procedure opCode opPayload opView:=
  (identity opPayload).precompose opView
noncomputable def opGateP : Procedure opCode gateCode Op.gate:=
  (first gateCode (listCode Nat.bits)).comp opViewP
noncomputable def opWiresP : Procedure opCode (listCode Nat.bits) Op.wires:=
  (second gateCode (listCode Nat.bits)).comp opViewP
noncomputable def wireWordsP : Procedure (prodCode unaryCode (listCode Nat.bits)) id
    (fun x=>x.2.flatMap (fun i=>natWord (min x.1 i))) :=
  (listJoinWords.comp (listMapWith (f:=fun cap i=>natWord (min cap i)) 0 []
    (natWordP.comp clippedUnary))).congrFun (by intro x;rfl)
noncomputable def opEncodeClippedP : Procedure (prodCode unaryCode opCode) id
    (fun x=>x.2.encodeClipped x.1) := by
  let cap:=first unaryCode opCode
  let o:=second unaryCode opCode
  let header:=gateHeaderP.comp (opGateP.comp o)
  let wires:=wireWordsP.comp (cap.pair (opWiresP.comp o))
  exact (append.comp (header.pair wires)).congrFun (by intro x;rfl)
noncomputable def dataViewP : Procedure dataCode dataPayload dataView:=
  (identity dataPayload).precompose dataView
noncomputable def qubitsP : Procedure dataCode unaryCode Data.qubits:=
  (first unaryCode (listCode opCode)).comp dataViewP
noncomputable def opsP : Procedure dataCode (listCode opCode) Data.ops:=
  (second unaryCode (listCode opCode)).comp dataViewP
noncomputable def encodeClippedP : Procedure dataCode id Data.encodeClipped := by
  let qword:=natWordP.comp qubitsP
  let len:=(NativeAIG.Emission.listUnaryLength opCode ⟨plainGate .not,[]⟩).comp opsP
  let nword:=natWordP.comp len
  let words:=(listMapWith (f:=fun cap (o : Op)=>o.encodeClipped cap)
    ⟨plainGate .not,[]⟩ [] opEncodeClippedP).comp (qubitsP.pair opsP)
  let payload:=listJoinWords.comp words
  exact (append.comp ((append.comp (qword.pair nword)).pair payload)).congrFun (by intro x;rfl)
end Emission

/-- This reduction charges all unary description writing, including every wire.
It is useful only with an actual finite-stack emitter for the literal erased family. -/
theorem uniform_of_emitter (family : ℕ→Circuit)
    (p : Procedure unaryCode dataCode (fun n=>erase (family n))) : Uniform family := by
  let pp : Procedure unaryCode Circuit.encode family:=
    (Emission.encodeClippedP.comp p).result (by intro n;exact erase_encodeClipped (family n))
  exact ⟨pp.toTM2,pp.toTM2_finite⟩
end ExactQuantumFactoring.CircuitEmission

end


end OAI
