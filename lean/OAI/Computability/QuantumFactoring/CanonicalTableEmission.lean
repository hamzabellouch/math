import Mathlib
import OAI.Computability.QuantumFactoring.CanonicalResidueCircuit
import OAI.Computability.QuantumFactoring.TableArithmeticEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma dividesOn {p m : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hp : NetEmits ea p) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>BitArithmetic.dividesOn (p x) (m x)):=zeroWord hk hn ((hm.pair hp).comp (mod hn))
lemma leastDivisorTest {ps : ∀x,List (BooleanNetwork (k x) (n x))} {m p : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hps : NetsEmits ea ps)
    (hm : NetEmits ea m) (hp : NetEmits ea p) : NetEmits ea (fun x=>BitArithmetic.leastDivisorTest (ps x) (m x) (p x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  have ht:=(dividesOn (hk.comp hx.snd) (hn.comp hx.snd) hps.get (hm.compInput hx.snd)).bnot.bor
    (wordLe (hp.compInput hx.snd) hps.get (hn.comp hx.snd))
  exact (hps.map (g:=fun x q=>(BitArithmetic.dividesOn q (m x)).bnot.bor (BitArithmetic.wordLe (p x) q)) ht).all hk
lemma componentCongruence {ps : ∀x,List (BooleanNetwork (k x) (n x))} {a m p : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hps : NetsEmits ea ps)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.componentCongruence (ps x) (a x) (m x) (p x)):=by
  have hq:=primeComponent hk hn hm hp
  have h1:=wordConst hk hn (const _ _ 1)
  exact ((ha.pair hq).comp (mod hn)).equalOn
    ((leastDivisorTest hk hn hps hm hp).wordMux h1 (natSubOn hk hn hq h1) hn) hn
lemma tableCanonical {ps : ∀x,List (BooleanNetwork (k x) (n x))} {a m : ∀x,BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hps : NetsEmits ea ps)
    (ha : NetEmits ea a) (hm : NetEmits ea m) : NetEmits ea (fun x=>BitArithmetic.tableCanonicalNet (ps x) (a x) (m x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  have hm':=hm.compInput hx.snd
  have ht:=(dividesOn (hk.comp hx.snd) (hn.comp hx.snd) hps.get hm').bnot.bor
    (componentCongruence (hk.comp hx.snd) (hn.comp hx.snd) (hps.comp hx.snd) (ha.compInput hx.snd) hm' hps.get)
  exact (wordLt ha hm hn).band ((hps.map (g:=fun x p=>(BitArithmetic.dividesOn p (m x)).bnot.bor
    (BitArithmetic.componentCongruence (ps x) (a x) (m x) p)) ht).all hk)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
