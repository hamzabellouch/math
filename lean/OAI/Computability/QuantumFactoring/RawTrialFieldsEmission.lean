import Mathlib
import OAI.Computability.QuantumFactoring.OrderSamplerEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k u s n b : α→ℕ}
lemma left (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BooleanNetwork.leftNet (u x) (b x)):=
  selectSlice (hu.unaryAdd hb) hu (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma right (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BooleanNetwork.rightNet (u x) (b x)):=
  selectSlice (hu.unaryAdd hb) hb hu.unaryNat _ (by intros;rfl)
lemma toWidth {f : ∀x,BooleanNetwork (k x) (u x)} (hf : NetEmits ea f)
    (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderTrial.toWidth (b x) (f x)):=hf.comp (resize hu hb)
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.RawTrialEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u s n : α→ℕ}
variable {r : ∀x,BooleanNetwork (k x) (OrderTrial.rawWidth (u x) (s x) (n x))}
lemma mode (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawMode (r x)):=
  hr.comp (left (const _ _ 2) ((OrderSamplerEmission.width hu (hs.unaryAdd (const _ _ 2))).unaryAdd (OrderSamplerEmission.guessWidth hn)))
lemma sample (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawSample (r x)):=by
  have hw:=OrderSamplerEmission.width hu (hs.unaryAdd (const _ _ 2))
  have hg:=OrderSamplerEmission.guessWidth hn
  exact (hr.comp (right (const _ _ 2) (hw.unaryAdd hg))).comp (left hw hg)
lemma guesses (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawGuesses (r x)):=by
  have hw:=OrderSamplerEmission.width hu (hs.unaryAdd (const _ _ 2))
  have hg:=OrderSamplerEmission.guessWidth hn
  exact (hr.comp (right (const _ _ 2) (hw.unaryAdd hg))).comp (right hw hg)
lemma den (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawDen (r x)):=
  (guesses hu hs hn hr).comp (left hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))
lemma num (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawNum (r x)):=
  ((guesses hu hs hn hr).comp (right hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))).comp (left hn (hn.unaryAdd (retentionBits hn)))
lemma residue (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawResidue (r x)):=
  (((guesses hu hs hn hr).comp (right hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))).comp
    (right hn (hn.unaryAdd (retentionBits hn)))).comp (left hn (retentionBits hn))
lemma coin (hu : Emits ea unaryCode u) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderTrial.rawCoin (r x)):=
  (((guesses hu hs hn hr).comp (right hn (hn.unaryAdd (hn.unaryAdd (retentionBits hn))))).comp
    (right hn (hn.unaryAdd (retentionBits hn)))).comp (right hn (retentionBits hn))
end ExactQuantumFactoring.RawTrialEmission

end



end OAI
