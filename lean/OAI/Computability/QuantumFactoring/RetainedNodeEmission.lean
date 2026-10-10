import Mathlib
import OAI.Computability.QuantumFactoring.DescendingPrefixAutomatic
import OAI.Computability.QuantumFactoring.RetainedSplitFilterEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalNodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n s t : α→ℕ}
lemma previous (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) :
    NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).previousNet (t x)):=
  (firstSelect (((width hn hs ht).unaryAdd (PhysicalSplitEmission.width hn)).unaryAdd (initWork hn hs))
    (configWidth hn hs) (updateWork hn hs)).comp (firstSelect (width hn hs ht) (PhysicalSplitEmission.width hn) (initWork hn hs))
lemma lastSplit (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) :
    NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).lastSplitNet (t x)):=
  (firstSelect (((width hn hs ht).unaryAdd (PhysicalSplitEmission.width hn)).unaryAdd (initWork hn hs))
    (configWidth hn hs) (updateWork hn hs)).comp (targetSelect (width hn hs ht) (PhysicalSplitEmission.width hn) (initWork hn hs))
end ExactQuantumFactoring.PhysicalNodeEmission
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t s : α→ℕ}
lemma nodePrefix_eq {n t : ℕ} (hn : 0<n) (s : ℕ) (v : BooleanNetwork ((PhysicalTree.machine n).width t) ((PhysicalNode.machine n (2*n)).width s)) :
    filterPrefix (fun s=>(PhysicalNode.machine n (2*n)).previousNet s)
      (fun s v=>(PhysicalTree.machine n).retainedSplitFilter hn t (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s))) s v=
      (PhysicalTree.machine n).nodePrefixFilter hn t s v:=by
  induction s with
  | zero=>rfl
  | succ s ih=>dsimp only [filterPrefix,NodeMachine.nodePrefixFilter];rw [ih]
lemma nodePrefixFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) ((PhysicalNode.machine (n x) (2*n x)).width (s x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hs : Emits ea unaryCode s) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).nodePrefixFilter (hn0 x) (t x) (s x) (raw x)):=by
  have h2:=(const _ _ 2).unaryMul hn
  have hW:=PhysicalNodeEmission.width hn h2 hs
  have hep : NetEmits (prodCode ea unaryCode) (fun x=>(PhysicalNode.machine (n x.1) (2*n x.1)).previousNet x.2):=by
    have hx:=BitStackProgram.Emits.id (prodCode ea unaryCode)
    exact PhysicalNodeEmission.previous (hn.comp hx.fst) (h2.comp hx.fst) hx.snd
  have hec : NetEmits (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalNode.machine (n a) (2*n a)).width (j+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2)))
      (fun x=>(PhysicalTree.machine (n x.1)).retainedSplitFilter (hn0 x.1) (t x.1)
        (x.2.2.comp ((PhysicalNode.machine (n x.1) (2*n x.1)).lastSplitNet x.2.1))):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalNode.machine (n a) (2*n a)).width (j+1))=>(x.1,(x.2.1,erasePack x.2.2)))
    exact retainedSplitFilter (hn.comp hx.fst) (ht.comp hx.fst) (fun x=>hn0 x.1)
      ((ofCanonical hx.snd.snd).comp (PhysicalNodeEmission.lastSplit (hn.comp hx.fst) (h2.comp hx.fst) hx.snd.fst))
  have h:=filterPrefixEmits (fun x j=>(PhysicalNode.machine (n x) (2*n x)).previousNet j)
    (fun x j v=>(PhysicalTree.machine (n x)).retainedSplitFilter (hn0 x) (t x) (v.comp ((PhysicalNode.machine (n x) (2*n x)).lastSplitNet j)))
    (fun x j=>SplitMachine.previousNet_count _ j)
    (W:=fun x=>(PhysicalNode.machine (n x) (2*n x)).width (s x)) (fun x j hj=>by
      rw [SplitMachine.width_eq,SplitMachine.width_eq];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
    raw hs (machineWidth hn ht) hr hW.unaryPoly hep hec
  exact h.congr (fun x=>nodePrefix_eq (hn0 x) (s x) (raw x))
lemma retainedNodeFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (NodeKernel.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedNodeFilter (hn0 x) (t x) (raw x)):=
  nodePrefixFilter hn ht ((const _ _ 2).unaryMul hn) hn0 hr
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
