import Mathlib
import OAI.Computability.QuantumFactoring.NetworkModularPowerEmission
import OAI.Computability.QuantumFactoring.CyclicTestEmission
import OAI.Computability.QuantumFactoring.RootCircuitEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w k : α→ℕ}
lemma splitOn {a b : α→ℕ} {f : ∀x,BooleanNetwork (a x) (b x)}
    (c : α→Prop) [DecidablePred c] (hc : Emits ea Procedure.boolCode (fun x=>decide (c x)))
    (hy : NetEmits (fun x:{a // c a}=>ea x.val) (fun x=>f x.val))
    (hz : NetEmits (fun x:{a // ¬c a}=>ea x.val) (fun x=>f x.val)) : NetEmits ea f:=
  ofCanonical (BitStackProgram.Emits.splitOn c hc hy.canonical hz.canonical)
lemma constMod (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) :
    NetEmits ea (fun x=>BitArithmetic.constMod (w x) (s x)):=
  ((identity hw).pair (wordConst hw hw hs)).comp (mod hw)
lemma divides (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) :
    NetEmits ea (fun x=>dividesNet (w x) (s x)):=
  (constMod hw hs).equalOn (wordConst hw hw (const _ _ 0)) hw
lemma constPowMod (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) (hk : Emits ea Nat.bits k) :
    NetEmits ea (fun x=>BitArithmetic.constPowMod (w x) (s x) (k x)):=
  (((identity hw).pair (wordConst hw hw hs)).pair ((wordConst hw hw hk).reverseWord hw)).comp (modularPower hw hw)
lemma powerOne (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) (hk : Emits ea Nat.bits k) :
    NetEmits ea (fun x=>powerOneNet (w x) (s x) (k x)):=
  (constPowMod hw hs hk).equalOn (wordConst hw hw (const _ _ 1)) hw
lemma orderTests (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.orderTests (w x) (s x) (k x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact allOfFn hw hk (powerOne (hw.comp hx.snd) (hs.comp hx.snd) hx.fst.unarySucc.unaryNat).bnot
lemma properDivisor (hw : Emits ea unaryCode w) (hs : Emits ea Nat.bits s) :
    NetEmits ea (fun x=>BitArithmetic.properDivisor (w x) (s x)):=
  (divides hw hs).band ((wordConst hw hw hs).wordLt (identity hw) hw)
lemma noSmallDivisor (hw : Emits ea unaryCode w) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.noSmallDivisor (w x) (k x)):=by
  have hJ:=(hk.unaryNat.natSub (const _ _ 1)).boundedUnary hk (by intro x;exact Nat.sub_le _ _)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (k a-1)=>(x.2.val,x.1))
  exact allOfFn hw hJ (properDivisor (hw.comp hx.snd) (hx.fst.unaryNat.natAdd (const _ _ 2))).bnot
lemma allCongruences (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) [∀x,NeZero (s x)] :
    NetEmits ea (fun x=>BitArithmetic.allCongruences (s x) (w x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (8*s a)=>(x.2.val,x.1))
  exact allOfFn hw ((const _ _ 8).unaryMul hs) (cyclicTest (hs.comp hx.snd) (hw.comp hx.snd) hx.fst.unarySucc.unaryNat)
lemma aksBranch (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) [∀x,NeZero (s x)] :
    NetEmits ea (fun x=>BitArithmetic.aksBranch (n x) (s x)):=by
  have hw:=(hn.unaryMul hn).unarySucc
  exact ((divides hw hs.unaryNat).bnot.band (orderTests hw hs.unaryNat (hn.unaryPow 2))).band
    ((noSmallDivisor hw ((const _ _ 8).unaryMul hs)).band (allCongruences hs hw))
lemma aksStaticBranch (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) :
    NetEmits ea (fun x=>BitArithmetic.aksStaticBranch (n x) (s x)):=by
  apply splitOn (fun x=>(s x).Prime) hs.unaryPrime
  · have : ∀x:{a:α // (s a).Prime},NeZero (s x.val):=fun x=>⟨x.property.ne_zero⟩
    exact (aksBranch (hn.precompose Subtype.val) (hs.precompose Subtype.val)).congr
      (by intro x;simp only [BitArithmetic.aksStaticBranch,dite_eq_left x.property])
  · have hN:=hn.precompose (fun x:{a:α // ¬(s a).Prime}=>x.val)
    exact (constant (hN.unaryMul hN).unarySucc (const _ _ false)).congr
      (by intro x;simp only [BitArithmetic.aksStaticBranch,dite_eq_right x.property])
lemma primality (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>primalityNet (n x)):=by
  have hK:=(hn.unaryPow 8).unarySucc
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a^8+1)=>(x.2.val,x.1))
  exact (perfectPower hn).bnot.band (anyOfFn (hn.unaryMul hn).unarySucc hK
    (aksStaticBranch (hn.comp hx.snd) hx.fst))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
