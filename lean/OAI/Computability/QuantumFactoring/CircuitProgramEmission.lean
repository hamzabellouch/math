import Mathlib
import OAI.Computability.QuantumFactoring.TreeReadout
import OAI.Computability.QuantumFactoring.CircuitEmissionBasic
import OAI.Computability.QuantumFactoring.NetworkExpressionEmission

namespace OAI



section

namespace ExactQuantumFactoring
namespace NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m : α→ℕ}
lemma data {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea dataCode (fun x=>erase (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ((ofProcedure Emission.packValueP).comp hp).congr he
lemma count {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea unaryCode (fun x=>(f x).net.count):=by
  exact ((ofProcedure ((NativeAIG.Emission.listUnaryLength nodeCode (.constant false)).comp
    Emission.dataNodesP)).comp hf.data).congr (by intro x;exact eraseNet_length _)
lemma outLength {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea unaryCode m:=by
  exact ((ofProcedure ((NativeAIG.Emission.listUnaryLength Nat.bits 0).comp
    Emission.dataOutputsP)).comp hf.data).congr (by intro x;exact List.length_ofFn)
end NetworkEmission.NetEmits

namespace CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits

def oracleOnOps (a : NetworkEmission.Data) : List Op:=
  (oracleOps a).map (Op.map (BooleanNetwork.oracleIndex a.inputs a.outputs.length a.width))
lemma erase_oracleOn {n m r : ℕ} (a : BooleanNetwork n m) (hr : a.net.count≤r) :
    (BooleanNetwork.oracleOn a hr).map eraseOp=oracleOnOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.oracleOn,List.map_map]
  rw [show (eraseOp ∘ Instruction.place (BooleanNetwork.oraclePlacement a hr))=
    (fun o=>(eraseOp o).map (BooleanNetwork.oracleIndex n m a.width)) by
      funext o;exact eraseOp_place _ _ _ (fun _=>rfl)]
  change List.map ((Op.map (BooleanNetwork.oracleIndex n m a.width)) ∘ eraseOp) a.oracle=_
  rw [←List.map_map,erase_oracle]
  simp only [oracleOnOps,NetworkEmission.erase,List.length_ofFn,NetworkEmission.Data.width,
    NetworkEmission.eraseNet_length,←a.net.width_eq]
lemma erase_firstProgram {n m r : ℕ} (ops : List (Instruction n)) :
    (firstProgram m r ops).map eraseOp=ops.map eraseOp:=by
  simp only [firstProgram,List.map_map]
  apply List.map_congr_left
  intro o ho
  rw [Function.comp_apply,eraseOp_place _ _ id (fun _=>rfl)]
  simp [Op.map]
lemma erase_reverseProgram {q : ℕ} (ops : List (Instruction q)) :
    (ops.reverse.map Instruction.reverse).map eraseOp=(ops.map eraseOp).reverse.map Op.reverse:=by
  simp only [List.map_map,List.map_reverse]
  rfl

def phaseOp (n : ℕ) : Op:=⟨plainGate .phase,[n]⟩
lemma erase_phaseAt {q : ℕ} (i : Fin q) : eraseOp (phaseAt i)=phaseOp i.val:=rfl

def phaseOps (a : NetworkEmission.Data) : List Op:=
  oracleOnOps a++[phaseOp a.inputs,phaseOp a.inputs]++oracleOnOps a
lemma erase_phaseOracle {n r : ℕ} (a : BooleanNetwork n 1) (hr : a.net.count≤r) :
    (BooleanNetwork.phaseOracle a hr).map eraseOp=phaseOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.phaseOracle,List.map_append,List.map_cons,List.map_nil,erase_oracleOn,
    erase_phaseAt,BooleanNetwork.phaseTarget,phaseOps,NetworkEmission.erase]

def amplifyOps (ps : List Op) (a z : NetworkEmission.Data) : List Op:=
  ps++phaseOps a++ps.reverse.map Op.reverse++phaseOps z++ps
lemma erase_amplification {n r : ℕ} (ops : List (Instruction n))
    (a z : BooleanNetwork n 1) (ha : a.net.count≤r) (hz : z.net.count≤r) :
    (amplificationProgram ops a z ha hz).map eraseOp=
      amplifyOps (ops.map eraseOp) (NetworkEmission.erase a) (NetworkEmission.erase z):=by
  simp only [amplificationProgram,List.map_append,erase_firstProgram,erase_phaseOracle,
    erase_reverseProgram,amplifyOps]

namespace Emission
noncomputable def oracleIndexP : Procedure
    (prodCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits) Nat.bits
    (fun x=>BooleanNetwork.oracleIndex x.1.1 x.1.2.1 x.1.2.2 x.2):=by
  let e:=first (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let i:=second (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let n:=(first Nat.bits (prodCode Nat.bits Nat.bits)).comp e
  let m:=(first Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let w:=(second Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let input:=binaryLt.comp (i.pair n)
  let work:=binaryLt.comp (i.pair w)
  let wi:=binaryAdd.comp ((binaryAdd.comp (n.pair m)).pair (binarySub.comp (i.pair n)))
  let oi:=binaryAdd.comp (n.pair (binarySub.comp (i.pair w)))
  exact (conditional input i (conditional work wi oi)).congrFun (by intro x;simp [BooleanNetwork.oracleIndex])
noncomputable def oracleOnOpsP : Procedure NetworkEmission.dataCode (listCode opCode) oracleOnOps:=by
  let env:=NetworkEmission.Emission.dataInputP.pair
    (((listLength Nat.bits 0).comp NetworkEmission.Emission.dataOutputsP).pair NetworkEmission.Emission.dataWidthP)
  exact (opsMapWith (f:=fun (e:ℕ×ℕ×ℕ) i=>BooleanNetwork.oracleIndex e.1 e.2.1 e.2.2 i) oracleIndexP).comp (env.pair oracleOpsP)
noncomputable def phaseOpP : Procedure Nat.bits opCode phaseOp:=
  opPackP.comp ((constant Nat.bits gateCode (plainGate .phase)).pair
    ((listCons Nat.bits).comp ((identity Nat.bits).pair (constant Nat.bits (listCode Nat.bits) []))))
noncomputable def phaseOpsP : Procedure NetworkEmission.dataCode (listCode opCode) phaseOps:=by
  let p:=phaseOpP.comp NetworkEmission.Emission.dataInputP
  let mid:=(listCons opCode).comp (p.pair ((listCons opCode).comp (p.pair (constant _ (listCode opCode) []))))
  exact opsAppendP.comp ((opsAppendP.comp (oracleOnOpsP.pair mid)).pair oracleOnOpsP)
end Emission

abbrev OpsEmits {α : Type} (ea : α→List Bool) {q : α→ℕ} (p : ∀x,List (Instruction (q x))) : Prop:=
  Emits ea (listCode opCode) (fun x=>(p x).map eraseOp)
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q m r : α→ℕ}
lemma congr {p s : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (h : ∀x,p x=s x) : OpsEmits ea s:=
  BitStackProgram.Emits.congr hp (fun x=>congrArg (List.map eraseOp) (h x))
lemma append {p s : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hs : OpsEmits ea s) :
    OpsEmits ea (fun x=>p x++s x):=
  (hp.listAppend ⟨plainGate .not,[]⟩ hs).congr (fun _=>List.map_append.symm)
lemma first {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (m r : α→ℕ) :
    OpsEmits ea (fun x=>firstProgram (m x) (r x) (p x)):=BitStackProgram.Emits.congr hp (fun _=>(erase_firstProgram _).symm)
lemma reverse {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) :
    OpsEmits ea (fun x=>(p x).reverse.map Instruction.reverse):=
  ((ofProcedure Emission.opsReverseP).comp hp).congr (fun _=>(erase_reverseProgram _).symm)
lemma oracleOn {f : ∀x,BooleanNetwork (q x) (m x)} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count≤r x) : OpsEmits ea (fun x=>BooleanNetwork.oracleOn (f x) (h x)):=
  ((ofProcedure Emission.oracleOnOpsP).comp hf.data).congr (fun _=>(erase_oracleOn _ _).symm)
lemma phase {f : ∀x,BooleanNetwork (q x) 1} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count≤r x) : OpsEmits ea (fun x=>BooleanNetwork.phaseOracle (f x) (h x)):=
  ((ofProcedure Emission.phaseOpsP).comp hf.data).congr (fun _=>(erase_phaseOracle _ _).symm)
lemma amplify {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    {f g : ∀x,BooleanNetwork (q x) 1} (hf : NetworkEmission.NetEmits ea f) (hg : NetworkEmission.NetEmits ea g)
    (h : ∀x,(f x).net.count≤r x) (j : ∀x,(g x).net.count≤r x) :
    OpsEmits ea (fun x=>amplificationProgram (p x) (f x) (g x) (h x) (j x)):=
  ((((hp.first (fun _=>1) r).append (hf |> fun hf=>phase hf h)).append
    (hp.reverse.first (fun _=>1) r)).append (phase hg j)).append (hp.first (fun _=>1) r)
lemma readout {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    {f : ∀x,BooleanNetwork (q x) (m x)} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count≤r x) : OpsEmits ea (fun x=>readoutProgram (p x) (f x) (h x)):=
  (hp.first m r).append (oracleOn hf h)
end OpsEmits
end CircuitEmission
end ExactQuantumFactoring

end



end OAI
