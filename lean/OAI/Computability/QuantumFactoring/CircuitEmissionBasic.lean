import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionProcedures
import OAI.Computability.QuantumFactoring.BitStackListFlatten
import OAI.Computability.QuantumFactoring.CircuitBooleanEmission
import OAI.Computability.QuantumFactoring.CircuitEmissionEncoding
import OAI.Computability.QuantumFactoring.BitStackListMapIdx

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def opPackP : Procedure opPayload opCode (fun x=>Op.mk x.1 x.2):=
  (identity opPayload).result (by intro x;rfl)
noncomputable def dataPackP : Procedure dataPayload dataCode (fun x=>Data.mk x.1 x.2):=
  (identity dataPayload).result (by intro x;rfl)
noncomputable def gatePackP : Procedure gatePayload gateCode (fun x=>Gate.mk x.1 x.2.1 x.2.2):=
  (identity gatePayload).result (by intro x;rfl)
noncomputable def gateReverseP : Procedure gateCode gateCode Gate.reverse:=
  gatePackP.comp (gatePrimitiveP.pair ((boolNot.comp gateInverseP).pair gateControlledP))
noncomputable def opReverseP : Procedure opCode opCode Op.reverse:=
  opPackP.comp ((gateReverseP.comp opGateP).pair opWiresP)
noncomputable def opsReverseP : Procedure (listCode opCode) (listCode opCode)
    (fun xs=>xs.reverse.map Op.reverse):=
  (listMap ⟨plainGate .not,[]⟩ ⟨plainGate .not,[]⟩ opReverseP).comp (listReverse opCode ⟨plainGate .not,[]⟩)
noncomputable def opMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea opCode) opCode (fun x=>x.2.map (f x.1)):=by
  let a:=first ea opCode
  let o:=second ea opCode
  exact opPackP.comp ((opGateP.comp o).pair (((listMapWith 0 0 p)).comp (a.pair (opWiresP.comp o))))
noncomputable def opsMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode opCode)) (listCode opCode) (fun x=>x.2.map (Op.map (f x.1))):=
  listMapWith (f:=fun (a : α) (o : Op)=>o.map (f a)) ⟨plainGate .not,[]⟩ ⟨plainGate .not,[]⟩ (opMapWith p)
noncomputable def opsAppendP : Procedure (prodCode (listCode opCode) (listCode opCode)) (listCode opCode)
    (fun x=>x.1++x.2):=listAppend opCode ⟨plainGate .not,[]⟩
noncomputable def notOpP : Procedure Nat.bits opCode notOp:=by
  let wires:=(listCons Nat.bits).comp ((identity Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))
  exact opPackP.comp ((Procedure.constant Nat.bits gateCode (plainGate .not)).pair wires)
noncomputable def cnotOpP : Procedure (prodCode Nat.bits Nat.bits) opCode (fun x=>cnotOp x.1 x.2):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let tail:=(listCons Nat.bits).comp (b.pair (Procedure.constant _ (listCode Nat.bits) []))
  let wires:=(listCons Nat.bits).comp (a.pair tail)
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .cnot)).pair wires)
noncomputable def toffoliOpP : Procedure (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) opCode
    (fun x=>toffoliOp x.1 x.2.1 x.2.2):=by
  let a:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let rs:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let b:=(first Nat.bits Nat.bits).comp rs
  let c:=(second Nat.bits Nat.bits).comp rs
  let tail:=(listCons Nat.bits).comp (c.pair (Procedure.constant _ (listCode Nat.bits) []))
  let mid:=(listCons Nat.bits).comp (b.pair tail)
  let wires:=(listCons Nat.bits).comp (a.pair mid)
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .toffoli)).pair wires)
noncomputable def opSingletonP : Procedure opCode (listCode opCode) (fun o=>[o]):=
  (listCons opCode).comp ((identity opCode).pair (Procedure.constant opCode (listCode opCode) []))
noncomputable def nodeOpsP : Procedure (prodCode Nat.bits NetworkEmission.nodeCode) (listCode opCode)
    (fun x=>nodeOps x.1 x.2):=by
  let t:=first Nat.bits NetworkEmission.nodeCode
  let o:=second Nat.bits NetworkEmission.nodeCode
  let tag:=NetworkEmission.Emission.nodeTagP.comp o
  let eq (i : ℕ):=binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits i))
  let a:=NetworkEmission.Emission.nodeLhsP.comp o
  let b:=NetworkEmission.Emission.nodeRhsP.comp o
  let n:=opSingletonP.comp (notOpP.comp t)
  let c:=opSingletonP.comp (cnotOpP.comp (a.pair t))
  let neg:=opsAppendP.comp (c.pair n)
  let conj:=conditional (binaryEq.comp (a.pair b)) c
    (opSingletonP.comp (toffoliOpP.comp (a.pair (b.pair t))))
  let const:=conditional (NetworkEmission.Emission.nodeBoolP.comp o) n (Procedure.constant _ (listCode opCode) [])
  exact (conditional (eq 0) const (conditional (eq 1) c (conditional (eq 2) neg conj))).congrFun (by
    rintro ⟨t,o⟩
    cases o with
    | constant b=>cases b <;> rfl
    | copy i=>rfl
    | neg i=>rfl
    | conj a b=>simp only [Function.comp_apply,NetworkEmission.nodeView,decide_eq_true_eq,nodeOps];rfl)
noncomputable def netOpsP : Procedure (prodCode Nat.bits (listCode NetworkEmission.nodeCode)) (listCode opCode)
    (fun x=>netOps x.1 x.2):=by
  let n:=first Nat.bits (prodCode Nat.bits NetworkEmission.nodeCode)
  let rs:=second Nat.bits (prodCode Nat.bits NetworkEmission.nodeCode)
  let i:=(first Nat.bits NetworkEmission.nodeCode).comp rs
  let o:=(second Nat.bits NetworkEmission.nodeCode).comp rs
  let step:=nodeOpsP.comp ((binaryAdd.comp (n.pair i)).pair o)
  let xs:=listMapIdxWith (f:=fun n i o=>nodeOps (n+i) o) (.constant false) [] step
  exact (listFlatten opCode ⟨plainGate .not,[]⟩).comp xs
noncomputable def copyOpsP : Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode opCode)
    (fun x=>copyOps x.1 x.2):=by
  let n:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let rs:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let i:=(first Nat.bits Nat.bits).comp rs
  let a:=(second Nat.bits Nat.bits).comp rs
  let step:=cnotOpP.comp (a.pair (binaryAdd.comp (n.pair i)))
  exact listMapIdxWith (f:=fun n i a=>cnotOp a (n+i)) 0 ⟨plainGate .not,[]⟩ step
noncomputable def oracleOpsP : Procedure NetworkEmission.dataCode (listCode opCode) oracleOps:=by
  let n:=NetworkEmission.Emission.dataInputP
  let xs:=NetworkEmission.Emission.dataNodesP
  let os:=NetworkEmission.Emission.dataOutputsP
  let w:=NetworkEmission.Emission.dataWidthP
  let p:=netOpsP.comp (n.pair xs)
  exact opsAppendP.comp ((opsAppendP.comp (p.pair (copyOpsP.comp (w.pair os)))).pair (opsReverseP.comp p))
end Emission
end ExactQuantumFactoring.CircuitEmission

end



end OAI
