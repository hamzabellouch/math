import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma launchWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.launchWork (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (launchWork hn)
lemma launchProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.launchProgram (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
lemma slots (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.slots (n x)):=
  (((hn.unaryPow 5).unarySucc).unaryMul ((const _ _ 2).unaryMul hn)).unaryMul ((const _ _ 2).unaryMul (hn.unaryPow 2))
lemma padding (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.padding (n x)):=
  ((hn.unaryPow 10).unaryNat.natSub (slots hn).unaryNat).boundedUnary (hn.unaryPow 10) (fun _=>Nat.sub_le _ _)
lemma paddedWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.paddedWidth (n x)):=
  (launchWidth hn).unaryAdd (hn.tensorWidth (padding hn))
lemma padProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.padProgram (n x)):=
  (OpsEmits.hadamards hn (fun _=>le_rfl)).tensor hn (padding hn)
lemma paddedProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.paddedProgram (n x)):=
  OpsEmits.parallel (launchProgram hn) (padProgram hn) (launchWidth hn)
lemma quarterWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.quarterWidth (n x)):=
  completionWidth (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalTree.quarterProgram (n x)):=
  OpsEmits.completion (paddedProgram hn) (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma launchHistory (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.launchHistory (n x)):=
  targetSelect hn (width hn) (launchWork hn)
lemma launchInput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.launchInput (n x)):=
  firstSelect hn (width hn) (launchWork hn)
lemma paddedHistory (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedHistory (n x)):=
  (left (launchWidth hn) (hn.tensorWidth (padding hn))).comp (launchHistory hn)
lemma paddedInput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedInput (n x)):=
  (left (launchWidth hn) (hn.tensorWidth (padding hn))).comp (launchInput hn)
lemma paddedPad (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedPad (n x)):=
  right (launchWidth hn) (hn.tensorWidth (padding hn))
lemma padFlag (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.padFlag (n x)):=by
  apply allOfFn (hn.tensorWidth (padding hn)) (padding hn)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (PhysicalTree.padding (n a))=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact (zeroWord (hN.tensorWidth (padding hN)) hN (NetEmits.tensorSelect hN (padding hN) (fun x=>x.2) hx.fst.unaryNat)).bnot
lemma quarterOrd (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterOrd (n x)):=
  ordinaryWires (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterGuess (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterGuess (n x)):=
  guessWires (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterCoin (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterCoin (n x)):=
  retentionWires (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma quarterRare (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterRare (n x)):=
  rareNet (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
