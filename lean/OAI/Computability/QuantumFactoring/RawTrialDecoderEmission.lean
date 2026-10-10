import Mathlib
import OAI.Computability.QuantumFactoring.TrialControlEmission
import OAI.Computability.QuantumFactoring.RawTrialLabelEmission

namespace OAI



section
namespace ExactQuantumFactoring.RawTrialEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u s n : α→ℕ}
variable {r : ∀x,BooleanNetwork (k x) (OrderTrial.rawWidth (u x) (s x) (n x))} {a m : ∀x,BooleanNetwork (k x) (u x)}
lemma accept (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawAcceptNet (a x) (m x) (r x)):=by
  have hw:=decodeWidth hu hs hn
  exact TrialControlEmission.accept hk hw hn (ha.toWidth hu hw) (hm.toWidth hu hw)
    ((mode hu hs hn hr).toWidth (const _ _ 2) hw) (trialDen hk hu hs hn hr) (trialNum hk hu hs hn hr)
    ((residue hu hs hn hr).toWidth hn hw) ((coin hu hs hn hr).toWidth (retentionBits hn) hw)
    (SamplerDecodeEmission.selected hk hu (hs.unaryAdd (const _ _ 2)) ha hm (sample hu hs hn hr))
lemma value (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.trialValueNet (a x) (m x) (r x)):=by
  have hw:=decodeWidth hu hs hn
  exact (accept hk hu hs hn ha hm hr).wordMux (trialDen hk hu hs hn hr) (wordConst hk hw (const _ _ 0)) hw
lemma smallValue (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.trialSmallValueNet (a x) (m x) (r x)):=
  (value hk hu hs hn ha hm hr).comp (resize (decodeWidth hu hs hn) hn)
end ExactQuantumFactoring.RawTrialEmission

end



end OAI
