import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialFieldsEmission
import OAI.Computability.QuantumFactoring.RetentionTemplateEmission
import OAI.Computability.QuantumFactoring.LabelRecoveryEmission
import OAI.Computability.QuantumFactoring.SamplerDecodeEmission

namespace OAI



section
namespace ExactQuantumFactoring.RawTrialEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u s n : α→ℕ}
lemma decodeSteps (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>OrderTrial.decodeSteps (s x)):=
  ((const _ _ 2).unaryMul (hs.unaryAdd (const _ _ 3))).unarySucc
lemma decodeWidth (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    Emits ea unaryCode (fun x=>OrderTrial.decodeWidth (u x) (s x) (n x)):=
  ((((((hs.unaryAdd (const _ _ 3)).unaryMul (decodeSteps hs).unarySucc).unarySucc.unaryAdd hu).unaryAdd hn).unaryAdd
    (retentionBits hn)).unaryAdd (hs.unaryAdd (const _ _ 3))).unaryAdd (const _ _ 3)
variable {r : ∀x,BooleanNetwork (k x) (OrderTrial.rawWidth (u x) (s x) (n x))}
lemma recovered (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.recoveredPairNet (r x)):=by
  have hw:=decodeWidth hu hs hn
  have hp:=NetworkEmission.Emits.powTwo (hs.unaryAdd (const _ _ 2))
  have hb:=NetworkEmission.Emits.powTwo hn
  exact recovery hk hw (decodeSteps hs) (wordConst hk hw hp) (wordConst hk hw hb)
    (((sample hu hs hn hr).comp (SamplerDecodeEmission.sampleY hu (hs.unaryAdd (const _ _ 2)))).toWidth (hs.unaryAdd (const _ _ 2)) hw)
lemma pair (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.trialPairNet (r x)):=by
  have hw:=decodeWidth hu hs hn
  exact (((mode hu hs hn hr).toWidth (const _ _ 2) hw).wordLt (wordConst hk hw (const _ _ 2)) hw).wordMux
    (recovered hk hu hs hn hr) (((den hu hs hn hr).toWidth hn hw).pair ((num hu hs hn hr).toWidth hn hw)) (hw.unaryAdd hw)
lemma trialDen (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.trialDenNet (r x)):=
  (pair hk hu hs hn hr).comp (left (decodeWidth hu hs hn) (decodeWidth hu hs hn))
lemma trialNum (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (hr : NetEmits ea r) : NetEmits ea (fun x=>OrderTrial.trialNumNet (r x)):=
  (pair hk hu hs hn hr).comp (right (decodeWidth hu hs hn) (decodeWidth hu hs hn))
end ExactQuantumFactoring.RawTrialEmission

end



end OAI
