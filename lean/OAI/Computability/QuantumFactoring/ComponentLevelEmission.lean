import Mathlib
import OAI.Computability.QuantumFactoring.ComponentPhiCircuit
import OAI.Computability.QuantumFactoring.CanonicalTableEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n t : α→ℕ}
lemma oddPart {a : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ha : NetEmits ea a) : NetEmits ea (fun x=>BitArithmetic.oddPartNet (a x)):=
  (ha.pair (primeComponent hk hn ha (wordConst hk hn (const _ _ 2)))).comp (div hn)
lemma closedLevel {a : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.closedLevelNet (a x) (t x)):=by
  have ht':=(ht.unaryNat.natSub (const _ _ 1)).boundedUnary ht (fun _=>Nat.sub_le ..)
  have hb:=((ha.comp (divides hn (Emits.powTwo ht))).wordMux
    (((oddPart hk hn ha).pair (wordConst hk hn (Emits.powTwo ht'))).comp (mul hn))
    (wordConst hk hn (const _ _ 0)) hn)
  have h:=ite (ht.unaryNat.natEq (const _ _ 0)) (oddPart hk hn ha)
    (ite (ht.unaryNat.natLt hn.unaryNat) hb (wordConst hk hn (const _ _ 0)))
  exact h.congr (by intro x;simp only [decide_eq_true_eq];rfl)
lemma componentPhi {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.componentPhiNet (m x) (p x)):=by
  have hq:=primeComponent hk hn hm hp
  exact natSubOn hk hn hq ((hq.pair hp).comp (div hn))
lemma componentLevel {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.componentLevelNet (m x) (p x) (t x)):=
  (dividesOn hk hn hp hm).wordMux (closedLevel hk hn ht (componentPhi hk hn hm hp))
    (wordConst hk hn (const _ _ 1)) hn
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
