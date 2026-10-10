import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma previous (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).previousNet (t x)):=
  (firstSelect (((machineWidth hn ht).unaryAdd (PhysicalNodeEmission.kernelWidth hn)).unaryAdd (initWork hn))
    (configWidth hn) (updateWork hn)).comp (firstSelect (machineWidth hn ht) (PhysicalNodeEmission.kernelWidth hn) (initWork hn))
lemma lastNode (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).lastNodeNet (t x)):=
  (firstSelect (((machineWidth hn ht).unaryAdd (PhysicalNodeEmission.kernelWidth hn)).unaryAdd (initWork hn))
    (configWidth hn) (updateWork hn)).comp (targetSelect (machineWidth hn ht) (PhysicalNodeEmission.kernelWidth hn) (initWork hn))
lemma firstNode (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).firstNodeNet (t x)):=by
  apply boundedStages ht (f:=fun x j=>(PhysicalTree.machine (n x)).firstNodeNet j)
  · exact lastNode hn (const _ _ 0)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((PhysicalTree.machine (n x.1)).firstNodeNet x.2.val))))
    exact (previous (hn.comp hx.fst) hx.snd.fst.unarySucc).comp (ofCanonical hx.snd.snd)
  · exact ((machineWidth hn ht.unarySucc).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [NodeMachine.width_eq,NodeMachine.width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · exact (PhysicalNodeEmission.kernelWidth hn).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact (PolyAt.const _ 0).of_le (fun x=>by rw [NodeMachine.firstNodeNet_count])
lemma flattenWords (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.flattenWords (n x)):=by
  apply wordBlocks (hn.tensorWidth hn) hn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat
lemma rootFlat (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>PhysicalTree.rootFlat (n x) (t x)):=by
  apply NetEmits.splitOn (fun x=>t x=0) (ht.unaryNat.natEq (const _ _ 0))
  · let inc:{x:α // t x=0}→α:=Subtype.val
    have hN:=hn.precompose inc
    have h:=(zeros (configWidth hN) (hN.unaryMul hN))
    obtain ⟨p,hp,he⟩:=h
    refine ⟨p,hp,?_⟩
    intro x
    have hx : t x.val=0:=x.property
    have hh:=he x
    dsimp only [inc] at hh
    change (p x).val.value=erase (PhysicalTree.rootFlat (n x.val) (t x.val))
    rw [hx]
    exact hh
  · let inc:{x:α // ¬t x=0}→α:=Subtype.val
    have hN:=hn.precompose inc
    have hT:=ht.precompose inc
    have hg:=(hT.unaryNat.natSub (const _ _ 1)).boundedUnary hT (fun _=>Nat.sub_le _ _)
    have h:=((firstNode hN hg).comp (nodeResult hN)).comp (flattenWords hN)
    obtain ⟨p,hp,he⟩:=h
    refine ⟨p,hp,?_⟩
    intro x
    have hx : t x.val=(t x.val-1)+1:=by have:=x.property;omega
    have hh:=he x
    dsimp only [inc] at hh
    change (p x).val.value=erase (PhysicalTree.rootFlat (n x.val) (t x.val))
    conv_rhs => rw [hx]
    exact hh
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
