import Mathlib
import OAI.Computability.QuantumFactoring.OrderSamplerEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalOrderEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma samplerZero (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSlots.samplerZeroNet (w x) (b x)):=by
  have hi:=hw.unaryAdd hw
  exact ((identity hi).pair (zeros hi (TriangularEmission.width hb))).packNet
    (zeros hi hw) hi (OrderSamplerEmission.scratch hw hb)
lemma rawZero (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>OrderSlots.rawZeroNet (n x)):=
  (zeros (hn.unaryAdd hn) (const _ _ 2)).pair
    ((samplerZero hn ((sampleExponent hn).unaryAdd (const _ _ 2))).pair
      (zeros (hn.unaryAdd hn) (OrderSamplerEmission.guessWidth hn)))
lemma ordinaryWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.ordinaryWidth (n x)):=
  (OrderSamplerEmission.rawWidth hn (sampleExponent hn) hn).tensorWidth (hn.unaryPow 5)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.width (n x)):=
  completionWidth (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderSlots.program (n x)):=
  OpsEmits.completion (OpsEmits.tensor (OrderSamplerEmission.rawProgram hn (sampleExponent hn) hn)
    (OrderSamplerEmission.rawWidth hn (sampleExponent hn) hn) (hn.unaryPow 5))
    (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>OrderSlots.initialNet (n x)):=by
  apply completionInitial (hn.unaryAdd hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
  apply tensor (hn.unaryAdd hn) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact rawZero (hn.comp hx.snd)
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.work (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.launchWidth (n x)):=
  ((hn.unaryAdd hn).unaryAdd (width hn)).unaryAdd (work hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderSlots.launch (n x)):=
  OpsEmits.prepared (initial hn) (hn.unaryAdd hn) (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalOrderEmission

end



end OAI
