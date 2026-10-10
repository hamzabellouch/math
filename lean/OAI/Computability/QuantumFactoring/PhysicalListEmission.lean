import Mathlib
import OAI.Computability.QuantumFactoring.TensorEmission
import OAI.Computability.QuantumFactoring.CompletionPreparationEmission
import OAI.Computability.QuantumFactoring.ListSamplerEmission

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma transitionWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>Completion.transitionWidth (n x)):=
  hn.unaryMul ((hn.unaryPow 5).unaryAdd (const _ _ 1))
lemma sampleExponent (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.sampleExponent (n x)):=by
  have h:=(const _ unaryCode 16).unaryMul hn
  exact (h.unaryNat.natSub (const _ _ 2)).boundedUnary h (fun _=>Nat.sub_le _ _)
lemma retentionBits (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.retentionBits (n x)):=
  ((const _ _ 80).unaryMul hn).unaryAdd (const _ _ 20)
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.PhysicalListEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma ordinaryWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.ordinaryWidth (n x)):=
  (ListSamplerEmission.width hn).tensorWidth (hn.unaryPow 5)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.width (n x)):=
  completionWidth (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalListSlots.program (n x)):=
  OpsEmits.completion (OpsEmits.tensor (ListSamplerEmission.program hn) (ListSamplerEmission.width hn) (hn.unaryPow 5))
    (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.initialNet (n x)):=by
  apply completionInitial hn (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
  apply tensor hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact ListSamplerEmission.singleZero (hn.comp hx.snd)
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.work (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (work hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalListSlots.launch (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalListEmission

end



end OAI
