import Mathlib
import OAI.Computability.QuantumFactoring.RetainedQuarterPolynomial
import OAI.Computability.QuantumFactoring.TreePreparationEmission
import OAI.Computability.QuantumFactoring.TreeHistoryEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma current (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).currentNet (t x)):=
  NodeMachineEmission.current (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma rowQuery (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).rowQuery (t x)):=
  ((previous hn ht).comp (current hn ht)).comp (query hn)
lemma rowFields (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits
    (fun x:Σa,Fin (n a)=>prodCode unaryCode ea (x.2.val,x.1))
    (fun x=>(PhysicalTree.machine (n x.1)).rowFields (t x.1) x.2):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  exact (lastNode (hn.comp hx.snd) (ht.comp hx.snd)).comp (fields hn)
lemma rowVerified (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).rowVerifiedNet (t x)):=
  (zeroWord (machineWidth hn ht.unarySucc) hn (rowQuery hn ht)).bor
    (factorVerifier (machineWidth hn ht.unarySucc) hn (rowQuery hn ht) (rowFields hn ht))
lemma verified (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).verifiedNet (t x)):=by
  apply boundedStages ht (f:=fun x j=>(PhysicalTree.machine (n x)).verifiedNet j)
  · exact constant (configWidth hn) (const _ _ true)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((PhysicalTree.machine (n x.1)).verifiedNet x.2.val))))
    exact ((previous (hn.comp hx.fst) hx.snd.fst).comp (ofCanonical hx.snd.snd)).band (rowVerified (hn.comp hx.fst) hx.snd.fst)
  · exact ((machineWidth hn ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [NodeMachine.width_eq,NodeMachine.width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · exact PolyAt.const _ 1
  · exact NodeMachine.verifiedNet_at (hn.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1))
      ((ht.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
      ((query hn).countPoly.pull (fun x:Σa,Fin (t a+1)=>x.1))
lemma guessVerifier (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>ExactQuantumFactoring.guessVerifier (n x)):=by
  apply factorVerifier (hn.unaryAdd (hn.unaryMul hn)) hn (left hn (hn.unaryMul hn))
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact selectSlice (hN.unaryAdd (hN.unaryMul hN)) hN (hN.unaryNat.natAdd (hN.unaryNat.natMul hx.fst.unaryNat)) _
    (by intro x j;change n x.1 + (j.val+n x.1*x.2.val)=n x.1+n x.1*x.2.val+j.val;omega)
lemma quarterGuessFlag (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterGuessFlag (n x)):=
  (((quarterOrd hn).comp (paddedInput hn)).pair (quarterGuess hn)).comp (guessVerifier hn)
lemma paddedOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedOutputNet (n x)):=
  (paddedHistory hn).comp (rootFlat hn (steps hn))
lemma quarterOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterOutputNet (n x)):=
  completionOutput (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11) (paddedOutput hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
