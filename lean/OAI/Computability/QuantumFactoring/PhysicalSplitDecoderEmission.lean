import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplitEmission
import OAI.Computability.QuantumFactoring.PhysicalOrderOutputEmission
import OAI.Computability.QuantumFactoring.SuppliedDivisorEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalSplitEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma launchWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.launchWires (n x)):=
  firstSelect (PhysicalListEmission.launchWidth hn) (ordersWidth hn) (work hn)
lemma allOrderWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.allOrderWires (n x)):=
  targetSelect (PhysicalListEmission.launchWidth hn) (ordersWidth hn) (work hn)
lemma modulus (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.modulusNet (n x)):=
  (launchWires hn).comp (modulusWires hn)
lemma actualBase (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.actualBaseNet (i x)):=
  (launchWires hn).comp (base hn i hi)
lemma actualOrderRaw (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.actualOrderRawNet (i x)):=
  (allOrderWires hn).comp (NetEmits.tensorSelect (PhysicalOrderEmission.width hn) (hn.unaryPow 5) i hi)
lemma actualOrder (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.actualOrderNet (i x)):=
  PhysicalOrderEmission.output (width hn) hn (actualBase hn i hi) (modulus hn) (actualOrderRaw hn i hi)
lemma divisor (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.divisorNet (n x)):=by
  apply suppliedBits (width hn) hn (BitStackProgram.Emits.transitionWidth hn) (hn.unaryPow 5)
    ((modulus hn).comp (resize hn hn.unarySucc))
  · have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
    have hN:=hn.comp hx.snd
    exact (actualBase hN (fun x=>x.2) hx.fst.unaryNat).comp (resize hN hN.unarySucc)
  · have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
    exact actualOrder (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
end ExactQuantumFactoring.PhysicalSplitEmission

end



end OAI
