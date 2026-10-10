import Mathlib
import OAI.Computability.QuantumFactoring.MachineWiringEmission
import OAI.Computability.QuantumFactoring.CompletionEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k q W t d : α→ℕ}
lemma completionInitial {f : ∀x,BooleanNetwork (k x) (q x)}
    (hk : Emits ea unaryCode k) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>Completion.initialNet (f x) (W x) (t x) (d x)):=
  (zeros hk ht).pair (hf.pair ((zeros hk hW).pair (zeros hk (coinBits hW ht hd))))
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q W t d : α→ℕ}
lemma completion {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    OpsEmits ea (fun x=>Completion.program (p x) (W x) (t x) (d x)):=
  parallel (hadamards ht (fun _=>le_rfl)) (parallel hp
    (parallel (hadamards hW (fun _=>le_rfl)) (hadamards (coinBits hW ht hd) (fun _=>le_rfl)) hW) hq) ht
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI
