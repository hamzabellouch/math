import Mathlib
import OAI.Computability.QuantumFactoring.TriangularNetworkEmission
import OAI.Computability.QuantumFactoring.TrialControlEmission
import OAI.Computability.QuantumFactoring.ContinuedFractionEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k w e : α→ℕ}
lemma zeroWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.zeroWord (a x)):=
  ha.equalOn (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)) hw
lemma evenOn {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.evenOn (a x)):=
  zeroWord hk hw ((ha.pair (wordConst hk hw (const _ _ 2))).comp (mod hw))
lemma halfWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.halfWord (a x)):=
  (ha.pair (wordConst hk hw (const _ _ 2))).comp (div hw)
lemma properOn {a d : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.properOn (a x) (d x)):=
  (((wordConst hk hw (const _ _ 1)).wordLt hd hw).band (hd.wordLt ha hw)).band
    (zeroWord hk hw ((ha.pair hd).comp (mod hw)))
lemma halfPowerBits {a m : ∀x,BooleanNetwork (k x) (w x)} {d : ∀x,BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.halfPowerBits (a x) (m x) (d x)):=
  ((ha.pair hm).pair (TrialControlEmission.reverse he (halfWord hk he hd))).comp (modularPower hw he)
lemma shiftedHalfBits {a m : ∀x,BooleanNetwork (k x) (w x)} {d : ∀x,BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.shiftedHalfBits (a x) (m x) (d x)):=
  ((((halfPowerBits hk hw he ha hm hd).pair hm).comp (add hw)).pair (wordConst hk hw (const _ _ 1))).comp (sub hw)
lemma candidateBits {a m : ∀x,BooleanNetwork (k x) (w x)} {d : ∀x,BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) :
    NetEmits ea (fun x=>BitArithmetic.candidateBits (a x) (m x) (d x)):=
  ((zeroWord hk he hd).bnot.band (evenOn hk he hd)).wordMux
    (((shiftedHalfBits hk hw he ha hm hd).pair hm).comp (gcd hw))
    (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)) hw
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
