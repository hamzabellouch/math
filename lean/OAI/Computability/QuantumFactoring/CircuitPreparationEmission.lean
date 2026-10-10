import Mathlib
import OAI.Computability.QuantumFactoring.CircuitFinalEmission

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

def hadamardOp (i : ℕ) : Op:=⟨plainGate .hadamard,[i]⟩
lemma erase_hadamardAt {q : ℕ} (i : Fin q) : eraseOp (hadamardAt i)=hadamardOp i.val:=rfl
lemma erase_hadamardPrefix (q k : ℕ) (h : k≤q) :
    (hadamardPrefix q k h).map eraseOp=(List.range k).map hadamardOp:=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [hadamardPrefix,List.map_append,ih,List.range_succ,List.map_append];rfl
namespace Emission
open Procedure
noncomputable def hadamardOpP : Procedure Nat.bits opCode hadamardOp:=by
  let wires:=(listCons Nat.bits).comp ((identity Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .hadamard)).pair wires)
noncomputable def hadamardPrefixP : Procedure unaryCode (listCode opCode)
    (fun k=>(List.range k).map hadamardOp):=
  (listMap 0 (hadamardOp 0) hadamardOpP).comp NetworkEmission.Emission.rangeP
end Emission
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q r m : α→ℕ}
lemma hadamards {k : α→ℕ} (hk : Emits ea unaryCode k) (h : ∀x,k x≤q x) :
    OpsEmits ea (fun x=>hadamardPrefix (q x) (k x) (h x)):=
  ((ofProcedure Emission.hadamardPrefixP).comp hk).congr (fun _=>(erase_hadamardPrefix _ _ _).symm)
lemma left {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (r : α→ℕ) :
    OpsEmits ea (fun x=>leftProgram (r x) (p x)):=by
  exact place hp (fun x=>leftRegister (q x) (r x)) (fun _ i=>i) (by intros;rfl)
    (BitStackProgram.Emits.id (prodCode ea Nat.bits)).snd
lemma right {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hr : Emits ea unaryCode r) :
    OpsEmits ea (fun x=>rightProgram (r x) (p x)):=by
  have he:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact place hp (fun x=>rightRegister (r x) (q x)) (fun x i=>r x+i) (by intros;rfl)
    ((hr.comp he.fst).unaryNat.natAdd he.snd)
lemma parallel {p : ∀x,List (Instruction (q x))} {s : ∀x,List (Instruction (r x))}
    (hp : OpsEmits ea p) (hs : OpsEmits ea s) (hq : Emits ea unaryCode q) :
    OpsEmits ea (fun x=>parallelProgram (p x) (s x)):=
  (hp.left r).append (hs.right hq)
lemma target {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hm : Emits ea unaryCode m) (r : α→ℕ) :
    OpsEmits ea (fun x=>targetProgram (m x) (r x) (p x)):=by
  have he:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact place hp (fun x=>targetRegister (m x) (q x) (r x)) (fun x i=>m x+i) (by intros;rfl)
    ((hm.comp he.fst).unaryNat.natAdd he.snd)
lemma prepared {f : ∀x,BooleanNetwork (m x) (q x)} (hf : NetworkEmission.NetEmits ea f)
    (hm : Emits ea unaryCode m) (h : ∀x,(f x).net.count≤r x)
    {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) :
    OpsEmits ea (fun x=>preparedOracle (f x) (h x) (p x)):=
  (oracleOn hf h).append (hp.target hm r)
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
