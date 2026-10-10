import Mathlib
import OAI.Computability.QuantumFactoring.BooleanAlgebra
import OAI.Computability.QuantumFactoring.NetworkEmissionProcedures

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def bit (n i : ℕ) : Data:=select n [i]
def constant (n : ℕ) (b : Bool) : Data:=node n (.constant b)
def bnot (a : Data) : Data:=comp a (node 1 (.neg 0))
def band (a b : Data) : Data:=comp (pair a b) (node 2 (.conj 0 1))
def bor (a b : Data) : Data:=bnot (band (bnot a) (bnot b))
def bxor (a b : Data) : Data:=bor (band a (bnot b)) (band (bnot a) b)
def mux (c a b : Data) : Data:=bor (band c a) (band (bnot c) b)
lemma erase_bit {n : ℕ} (i : Fin n) : erase (BooleanNetwork.bit i)=bit n i.val := by
  simp [BooleanNetwork.bit,erase_select,bit,List.ofFn_succ]
lemma erase_constant {n : ℕ} (b : Bool) : erase (BooleanNetwork.constant (n:=n) b)=constant n b:=
  erase_node _
lemma erase_bnot {n : ℕ} (a : BooleanNetwork n 1) : erase a.bnot=bnot (erase a):=by
  rw [BooleanNetwork.bnot,erase_comp,erase_node];rfl
lemma erase_band {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.band b)=band (erase a) (erase b):=by
  rw [BooleanNetwork.band,erase_comp,erase_pair,erase_node];rfl
lemma erase_bor {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.bor b)=bor (erase a) (erase b):=by
  rw [BooleanNetwork.bor,erase_bnot,erase_band,erase_bnot,erase_bnot];rfl
lemma erase_bxor {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.bxor b)=bxor (erase a) (erase b):=by
  rw [BooleanNetwork.bxor,erase_bor,erase_band,erase_band,erase_bnot,erase_bnot];rfl
lemma erase_mux {n : ℕ} (c a b : BooleanNetwork n 1) : erase (BooleanNetwork.mux c a b)=
    mux (erase c) (erase a) (erase b):=by
  rw [BooleanNetwork.mux,erase_bor,erase_band,erase_band,erase_bnot];rfl

namespace Emission
noncomputable def selectP : Procedure (prodCode Nat.bits (listCode Nat.bits)) dataCode
    (fun x=>select x.1 x.2):=
  (dataPackP.comp ((first Nat.bits (listCode Nat.bits)).pair
    ((Procedure.constant _ (listCode nodeCode) []).pair (second Nat.bits (listCode Nat.bits))))).congrFun (by intro x;rfl)
noncomputable def nodeP : Procedure (prodCode Nat.bits nodeCode) dataCode (fun x=>node x.1 x.2):=by
  let n:=first Nat.bits nodeCode
  let o:=second Nat.bits nodeCode
  let ns:=(listCons nodeCode).comp (o.pair (Procedure.constant _ (listCode nodeCode) []))
  let os:=(listCons Nat.bits).comp (n.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact (dataPackP.comp (n.pair (ns.pair os))).congrFun (by intro x;rfl)
noncomputable def pairIndexP : Procedure (prodCode (prodCode Nat.bits Nat.bits) Nat.bits) Nat.bits
    (fun x=>pairIndex x.1.1 x.1.2 x.2):=by
  let e:=first (prodCode Nat.bits Nat.bits) Nat.bits
  let n:=(first Nat.bits Nat.bits).comp e
  let w:=(second Nat.bits Nat.bits).comp e
  let i:=second (prodCode Nat.bits Nat.bits) Nat.bits
  exact (conditional (binaryLt.comp (i.pair n)) i (binaryAdd.comp (w.pair (binarySub.comp (i.pair n))))).congrFun (by
    intro x;unfold pairIndex;split <;> simp_all)
noncomputable def pairP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>pair x.1 x.2):=by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  let env:=(dataInputP.comp a).pair (dataWidthP.comp a)
  let mp:=nodeMapWith (f:=fun (e : ℕ×ℕ) i=>pairIndex e.1 e.2 i) pairIndexP
  let ns:=(listMapWith (f:=fun (e : ℕ×ℕ) (o : Node)=>o.map (pairIndex e.1 e.2)) (.constant false) (.constant false) mp).comp
    (env.pair (dataNodesP.comp b))
  let os:=(listMapWith (f:=fun (e : ℕ×ℕ) i=>pairIndex e.1 e.2 i) 0 0 pairIndexP).comp
    (env.pair (dataOutputsP.comp b))
  let nn:=(listAppend nodeCode (.constant false)).comp ((dataNodesP.comp a).pair ns)
  let oo:=(listAppend Nat.bits 0).comp ((dataOutputsP.comp a).pair os)
  exact (dataPackP.comp ((dataInputP.comp a).pair (nn.pair oo))).congrFun (by intro x;rfl)
noncomputable def bitP : Procedure (prodCode Nat.bits Nat.bits) dataCode (fun x=>bit x.1 x.2):=
  (selectP.comp ((first Nat.bits Nat.bits).pair
    ((listCons Nat.bits).comp ((second Nat.bits Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))))).congrFun (by intro x;rfl)
noncomputable def constantP : Procedure (prodCode Nat.bits boolCode) dataCode (fun x=>constant x.1 x.2):=
  (nodeP.comp ((first Nat.bits boolCode).pair (nodeConstP.comp (second Nat.bits boolCode)))).congrFun (by intro x;rfl)
noncomputable def bnotP : Procedure dataCode dataCode bnot:=
  compP.comp ((identity dataCode).pair (Procedure.constant _ dataCode (node 1 (.neg 0))))
noncomputable def bandP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>band x.1 x.2):=
  compP.comp (pairP.pair (Procedure.constant _ dataCode (node 2 (.conj 0 1))))
noncomputable def borP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>bor x.1 x.2):=
  bnotP.comp (bandP.comp ((bnotP.comp (first dataCode dataCode)).pair (bnotP.comp (second dataCode dataCode))))
noncomputable def bxorP : Procedure (prodCode dataCode dataCode) dataCode (fun x=>bxor x.1 x.2):=by
  let a:=first dataCode dataCode
  let b:=second dataCode dataCode
  exact borP.comp ((bandP.comp (a.pair (bnotP.comp b))).pair (bandP.comp ((bnotP.comp a).pair b)))
noncomputable def muxP : Procedure (prodCode dataCode (prodCode dataCode dataCode)) dataCode
    (fun x=>mux x.1 x.2.1 x.2.2):=by
  let c:=first dataCode (prodCode dataCode dataCode)
  let a:=(first dataCode dataCode).comp (second dataCode (prodCode dataCode dataCode))
  let b:=(second dataCode dataCode).comp (second dataCode (prodCode dataCode dataCode))
  exact borP.comp ((bandP.comp (c.pair a)).pair (bandP.comp ((bnotP.comp c).pair b)))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
