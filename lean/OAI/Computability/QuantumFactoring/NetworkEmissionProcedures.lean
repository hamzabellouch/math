import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionPair
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def nodeView : Node→ℕ×Bool×ℕ×ℕ
  | .constant b=>(0,b,0,0)
  | .copy i=>(1,false,i,0)
  | .neg i=>(2,false,i,0)
  | .conj i j=>(3,false,i,j)
def nodePayload:=prodCode Nat.bits (prodCode boolCode (prodCode Nat.bits Nat.bits))
def nodeCode (o : Node) : List Bool:=nodePayload (nodeView o)
def dataView (a : Data) := (a.inputs,a.nodes,a.outputs)
def dataPayload:=prodCode Nat.bits (prodCode (listCode nodeCode) (listCode Nat.bits))
def dataCode (a : Data) : List Bool:=dataPayload (dataView a)

namespace Emission
noncomputable def nodeViewP : Procedure nodeCode nodePayload nodeView:=
  (identity nodePayload).precompose nodeView
noncomputable def nodeTagP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).1):=
  (first Nat.bits _).comp nodeViewP
noncomputable def nodeBoolP : Procedure nodeCode boolCode (fun o=>(nodeView o).2.1):=
  (first boolCode _).comp ((second Nat.bits _).comp nodeViewP)
noncomputable def nodeLhsP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).2.2.1):=
  (first Nat.bits Nat.bits).comp ((second boolCode _).comp ((second Nat.bits _).comp nodeViewP))
noncomputable def nodeRhsP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).2.2.2):=
  (second Nat.bits Nat.bits).comp ((second boolCode _).comp ((second Nat.bits _).comp nodeViewP))
noncomputable def nodeConstP : Procedure boolCode nodeCode Node.constant:=
  ((Procedure.constant boolCode Nat.bits 0).pair ((identity boolCode).pair
    ((Procedure.constant boolCode Nat.bits 0).pair (Procedure.constant boolCode Nat.bits 0)))).result (by intro b;rfl)
noncomputable def nodeCopyP : Procedure Nat.bits nodeCode Node.copy:=
  ((Procedure.constant Nat.bits Nat.bits 1).pair ((Procedure.constant Nat.bits boolCode false).pair
    ((identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 0)))).result (by intro i;rfl)
noncomputable def nodeNegP : Procedure Nat.bits nodeCode Node.neg:=
  ((Procedure.constant Nat.bits Nat.bits 2).pair ((Procedure.constant Nat.bits boolCode false).pair
    ((identity Nat.bits).pair (Procedure.constant Nat.bits Nat.bits 0)))).result (by intro i;rfl)
noncomputable def nodeConjP : Procedure (prodCode Nat.bits Nat.bits) nodeCode (fun x=>Node.conj x.1 x.2):=
  ((Procedure.constant _ Nat.bits 3).pair ((Procedure.constant _ boolCode false).pair (identity _))).result (by intro x;rfl)

noncomputable def nodeMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea nodeCode) nodeCode (fun x=>x.2.map (f x.1)) := by
  let a:=first ea nodeCode
  let o:=second ea nodeCode
  let tag:=nodeTagP.comp o
  let isTag:=(fun k=>binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits k)))
  let lhs:=p.comp (a.pair (nodeLhsP.comp o))
  let rhs:=p.comp (a.pair (nodeRhsP.comp o))
  let b:=nodeConstP.comp (nodeBoolP.comp o)
  let c:=nodeCopyP.comp lhs
  let n:=nodeNegP.comp lhs
  let g:=nodeConjP.comp (lhs.pair rhs)
  exact (conditional (isTag 0) b (conditional (isTag 1) c (conditional (isTag 2) n g))).congrFun (by
    rintro ⟨a,o⟩;cases o <;> rfl)
noncomputable def dataViewP : Procedure dataCode dataPayload dataView:=
  (identity dataPayload).precompose dataView
noncomputable def dataInputP : Procedure dataCode Nat.bits Data.inputs:=
  (first Nat.bits _).comp dataViewP
noncomputable def dataNodesP : Procedure dataCode (listCode nodeCode) Data.nodes:=
  (first (listCode nodeCode) _).comp ((second Nat.bits _).comp dataViewP)
noncomputable def dataOutputsP : Procedure dataCode (listCode Nat.bits) Data.outputs:=
  (second (listCode nodeCode) _).comp ((second Nat.bits _).comp dataViewP)
noncomputable def dataPackP : Procedure dataPayload dataCode (fun x=>Data.mk x.1 x.2.1 x.2.2):=
  (identity dataPayload).result (by intro x;rfl)
noncomputable def dataWidthP : Procedure dataCode Nat.bits (fun a=>a.inputs+a.nodes.length):=
  binaryAdd.comp (dataInputP.pair ((listLength nodeCode (.constant false)).comp dataNodesP))

abbrev indexCode:=prodCode Nat.bits (listCode Nat.bits)
noncomputable def attachIndexP : Procedure (prodCode indexCode Nat.bits) Nat.bits
    (fun x=>attachRawIndex x.1.1 x.1.2 x.2) := by
  let env:=first indexCode Nat.bits
  let width:=(first Nat.bits (listCode Nat.bits)).comp env
  let rho:=(second Nat.bits (listCode Nat.bits)).comp env
  let i:=second indexCode Nat.bits
  let len:=(listLength Nat.bits 0).comp rho
  let off:=binarySub.comp (i.pair len)
  let test:=binaryLt.comp (i.pair len)
  let get:=(listGet Nat.bits 0).comp (i.pair rho)
  exact (conditional test get (binaryAdd.comp (width.pair off))).congrFun (by
    intro x;unfold attachRawIndex;split <;> simp_all)
noncomputable def compP : Procedure (prodCode dataCode dataCode) dataCode
    (fun x=>comp x.1 x.2) := by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  let env:=(dataWidthP.comp a).pair (dataOutputsP.comp a)
  let ns:=(listMapWith (f:=fun (e : ℕ×List ℕ) (o : Node)=>o.map (attachRawIndex e.1 e.2)) (Node.constant false) (Node.constant false) (nodeMapWith (f:=fun (e : ℕ×List ℕ) i=>attachRawIndex e.1 e.2 i) attachIndexP)).comp
    (env.pair (dataNodesP.comp b))
  let nodes:=(listAppend nodeCode (.constant false)).comp ((dataNodesP.comp a).pair ns)
  let outs:=(listMapWith (f:=fun (e : ℕ×List ℕ) i=>attachRawIndex e.1 e.2 i) 0 0 attachIndexP).comp (env.pair (dataOutputsP.comp b))
  exact (dataPackP.comp ((dataInputP.comp a).pair (nodes.pair outs))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
