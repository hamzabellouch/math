import Mathlib
import OAI.Computability.QuantumFactoring.RetainedNodeEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t s : α→ℕ}
lemma treePrefix_eq {n t : ℕ} (hn : 0<n) (s : ℕ) (v : BooleanNetwork ((PhysicalTree.machine n).width t) ((PhysicalTree.machine n).width s)) :
    filterPrefix (fun s=>(PhysicalTree.machine n).previousNet s)
      (fun s v=>(PhysicalTree.machine n).retainedNodeFilter hn t (v.comp ((PhysicalTree.machine n).lastNodeNet s))) s v=
      (PhysicalTree.machine n).treePrefixFilter hn t s v:=by
  induction s with
  | zero=>rfl
  | succ s ih=>dsimp only [filterPrefix,NodeMachine.treePrefixFilter];rw [ih]
lemma treePrefixFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) ((PhysicalTree.machine (n x)).width (s x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hs : Emits ea unaryCode s) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).treePrefixFilter (hn0 x) (t x) (s x) (raw x)):=by
  have hep : NetEmits (prodCode ea unaryCode) (fun x=>(PhysicalTree.machine (n x.1)).previousNet x.2):=by
    have hx:=BitStackProgram.Emits.id (prodCode ea unaryCode)
    exact previous (hn.comp hx.fst) hx.snd
  have hec : NetEmits (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalTree.machine (n a)).width (j+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2)))
      (fun x=>(PhysicalTree.machine (n x.1)).retainedNodeFilter (hn0 x.1) (t x.1)
        (x.2.2.comp ((PhysicalTree.machine (n x.1)).lastNodeNet x.2.1))):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalTree.machine (n a)).width (j+1))=>(x.1,(x.2.1,erasePack x.2.2)))
    exact retainedNodeFilter (hn.comp hx.fst) (ht.comp hx.fst) (fun x=>hn0 x.1)
      ((ofCanonical hx.snd.snd).comp (lastNode (hn.comp hx.fst) hx.snd.fst))
  have h:=filterPrefixEmits (fun x j=>(PhysicalTree.machine (n x)).previousNet j)
    (fun x j v=>(PhysicalTree.machine (n x)).retainedNodeFilter (hn0 x) (t x) (v.comp ((PhysicalTree.machine (n x)).lastNodeNet j)))
    (fun x j=>NodeMachine.previousNet_count _ j)
    (W:=fun x=>(PhysicalTree.machine (n x)).width (s x)) (fun x j hj=>by
      rw [NodeMachine.width_eq,NodeMachine.width_eq];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
    raw hs (machineWidth hn ht) hr (machineWidth hn hs).unaryPoly hep hec
  exact h.congr (fun x=>treePrefix_eq (hn0 x) (s x) (raw x))
lemma accepted (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).acceptedNet (hn0 x) (t x)):=
  (verified hn ht).band (treePrefixFilter hn ht ht hn0 (identity (machineWidth hn ht)))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
