import Mathlib
import OAI.Computability.QuantumFactoring.NetworkFoldChoiceEmission
import OAI.Computability.QuantumFactoring.PhysicalOrderEmission
import OAI.Computability.QuantumFactoring.RawTrialDecoderEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalOrderEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
variable {a m : ∀x,BooleanNetwork (k x) (n x)}
lemma usable (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>OrderSlots.usableOn (a x) (m x)):=
  (ha.wordLt hm hn).band (((ha.pair hm).comp (gcd hn)).equalOn (wordConst hk hn (const _ _ 1)) hn)
lemma result {r : ∀x,BooleanNetwork (k x) (OrderSlots.ordinaryWidth (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderSlots.orderResultNet (a x) (m x) (r x)):=by
  apply minimum hk hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  have hs:=sampleExponent hn'
  exact RawTrialEmission.smallValue (hk.comp hx.snd) hn' hs hn'
    (ha.compInput hx.snd) (hm.compInput hx.snd)
    ((hr.compInput hx.snd).comp (NetEmits.tensorSelect (OrderSamplerEmission.rawWidth hn' hs hn')
      (hn'.unaryPow 5) (fun x=>x.2) hx.fst.unaryNat))
lemma ordinary {r : ∀x,BooleanNetwork (k x) (OrderSlots.ordinaryWidth (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderSlots.ordinaryOn (a x) (m x) (r x)):=
  ((usable hk hn ha hm).wordMux (result hk hn ha hm hr) (wordConst hk hn (const _ _ 0)) hn).comp
    (resize hn (transitionWidth hn))
lemma output {r : ∀x,BooleanNetwork (k x) (OrderSlots.width (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hr : NetEmits ea r) :
    NetEmits ea (fun x=>OrderSlots.outputOn (a x) (m x) (r x)):=by
  have hq:=ordinaryWidth hn
  have hW:=transitionWidth hn
  have ht:=(const _ _ 2).unaryMul hn
  have hd:=(hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5)
  exact (hr.comp (rareNet hq hW ht hd)).wordMux (hr.comp (guessWires hq hW ht hd))
    (ordinary hk hn ha hm (hr.comp (ordinaryWires hq hW ht hd))) hW
end ExactQuantumFactoring.PhysicalOrderEmission

end



end OAI
