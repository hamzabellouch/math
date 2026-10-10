import Mathlib
import OAI.Computability.QuantumFactoring.CircuitPreparationEmission
import OAI.Computability.QuantumFactoring.EmissionDependentLists

namespace OAI



section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

def swapOps (n i : ℕ) : List Op:=[cnotOp i (n+i),cnotOp (n+i) i,cnotOp i (n+i)]
lemma erase_swapPrefix (n r k : ℕ) (h : k≤n) :
    (BooleanNetwork.swapPrefix n r k h).map eraseOp=((List.range k).map (swapOps n)).flatten:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [BooleanNetwork.swapPrefix,List.map_append,ih,List.range_succ,List.map_append,List.flatten_append]
    rfl
noncomputable def swapOpsP : Procedure (prodCode Nat.bits Nat.bits) (listCode opCode) (fun x=>swapOps x.1 x.2):=by
  have hx:=BitStackProgram.Emits.id (prodCode Nat.bits Nat.bits)
  have hi:=hx.snd
  have hj:=hx.fst.natAdd hi
  have ha:=(ofProcedure Emission.cnotOpP).comp (hi.pair hj)
  have hb:=(ofProcedure Emission.cnotOpP).comp (hj.pair hi)
  exact Classical.choice (ha.listCons (hb.listCons (ha.listCons (const _ _ []))))
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {n r : α→ℕ}
lemma swapBlocks (hn : Emits ea unaryCode n) :
    OpsEmits ea (fun x=>BooleanNetwork.swapPrefix (n x) (r x) (n x) le_rfl):=by
  have h:=(ofProcedure (Procedure.listMapWith (f:=swapOps) 0 [] swapOpsP)).comp (hn.unaryNat.pair hn.range)
  exact (h.flatten (⟨plainGate .not,[]⟩ : Op)).congr (fun _=>(erase_swapPrefix _ _ _ _).symm)
lemma cleanPermutation {f g : ∀x,BooleanNetwork (n x) (n x)}
    (hf : NetworkEmission.NetEmits ea f) (hg : NetworkEmission.NetEmits ea g)
    (hn : Emits ea unaryCode n) (h : ∀x,(f x).net.count≤r x) (j : ∀x,(g x).net.count≤r x) :
    OpsEmits ea (fun x=>BooleanNetwork.cleanPermutation (f x) (g x) (h x) (j x)):=
  ((oracleOn hf h).append (swapBlocks hn)).append (oracleOn hg j)
lemma singletonHadamard (i : ∀x,Fin (n x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    OpsEmits ea (fun x=>[hadamardAt (i x)]):=
  ((ofProcedure Emission.hadamardOpP).comp hi).listCons (const _ _ [])
lemma singletonPhase (i : ∀x,Fin (n x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    OpsEmits ea (fun x=>[phaseAt (i x)]):=
  ((ofProcedure Emission.phaseOpP).comp hi).listCons (const _ _ [])
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
