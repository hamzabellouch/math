import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalListOutputEmission
import OAI.Computability.QuantumFactoring.PhysicalOrderEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalSplitEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma ordersWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.ordersWidth (n x)):=
  (PhysicalOrderEmission.width hn).tensorWidth (hn.unaryPow 5)
lemma ordersProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.ordersProgram (n x)):=
  OpsEmits.tensor (PhysicalOrderEmission.program hn) (PhysicalOrderEmission.width hn) (hn.unaryPow 5)
lemma listWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.listWires (n x)):=
  targetSelect hn (PhysicalListEmission.width hn) (PhysicalListEmission.work hn)
lemma modulusWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.modulusWires (n x)):=
  firstSelect hn (PhysicalListEmission.width hn) (PhysicalListEmission.work hn)
lemma base (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.baseNet (i x)):=
  ((listWires hn).comp (PhysicalListEmission.output hn)).rewireSlice hn (hn.unaryNat.natMul hi) _
    (by intro x j; change j.val+n x*(i x).val=n x*(i x).val+j.val; omega)
lemma orderInitial (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.orderInitialNet (i x)):=
  ((base hn i hi).pair (modulusWires hn)).comp (PhysicalOrderEmission.initial hn)
lemma ordersInitial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.ordersInitialNet (n x)):=by
  apply tensor (PhysicalListEmission.launchWidth hn) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact orderInitial (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.work (n x)):=(ordersInitial hn).count
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.width (n x)):=
  ((PhysicalListEmission.launchWidth hn).unaryAdd (ordersWidth hn)).unaryAdd (work hn)
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.program (n x)):=
  OpsEmits.appendPrepared (PhysicalListEmission.launch hn) (ordersInitial hn)
    (PhysicalListEmission.launchWidth hn) (fun _=>le_rfl) (ordersProgram hn)
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.initialNet (n x)):=
  ((identity hn).packNet (zeros hn (PhysicalListEmission.width hn)) hn (PhysicalListEmission.work hn)).packNet
    (zeros hn (ordersWidth hn)) hn (work hn)
lemma launchWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.launchWork (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (launchWork hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.launch (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalSplitEmission

end



end OAI
