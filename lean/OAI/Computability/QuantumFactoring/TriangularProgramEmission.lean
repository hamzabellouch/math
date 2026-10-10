import Mathlib
import OAI.Computability.QuantumFactoring.CleanPermutationEmission
import OAI.Computability.QuantumFactoring.TriangularNetworkEmission

namespace OAI



section
namespace ExactQuantumFactoring.TriangularEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {b a : α→ℕ}
lemma work (hb : Emits ea unaryCode b) : Emits ea unaryCode (fun x=>Triangular.work (b x)):=
  ((const _ _ 159).unaryMul hb).unaryAdd (const _ _ 6)
lemma width (hb : Emits ea unaryCode b) : Emits ea unaryCode (fun x=>Triangular.width (b x)):=
  ((hb.unaryAdd hb).unaryAdd (hb.unaryAdd hb)).unaryAdd (work hb)
lemma preparePhase (hb : Emits ea unaryCode b) (h : ∀x,2≤b x) :
    OpsEmits ea (fun x=>ExactQuantumFactoring.preparePhase (b x) (h x)):=by
  have hOne:=(ofProcedure CircuitEmission.Emission.phaseOpP).comp (hb.unaryNat.natSub (const _ _ 1))
  have hTwo:=(ofProcedure CircuitEmission.Emission.phaseOpP).comp (hb.unaryNat.natSub (const _ _ 2))
  exact ((OpsEmits.hadamards hb (fun _=>le_rfl)).listAppend (⟨plainGate .not,[]⟩ : Op)
    (hOne.listCons (hOne.listCons (hTwo.listCons (const _ _ []))))).congr (by
      intro x;simp only [ExactQuantumFactoring.preparePhase,List.map_append,List.map_cons,List.map_nil];rfl)
lemma preparation (ha : Emits ea unaryCode a) :
    OpsEmits ea (fun x=>Triangular.preparation (a x)):=by
  have hb:=ha.unaryAdd (const _ _ 2)
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (preparePhase hb (by intro x;omega)).place (fun x=>Triangular.phaseRegister (a x+2))
    (fun x i=>a x+2+i) (by intros;rfl) ((hb.comp hx.fst).unaryNat.natAdd hx.snd)
lemma row (hb : Emits ea unaryCode b) (j : ∀x,Fin (b x))
    (hj : Emits ea Nat.bits (fun x=>(j x).val)) : OpsEmits ea (fun x=>Triangular.rowCircuit (j x)):=by
  have hR:=triangularRow hb j hj
  exact (OpsEmits.singletonHadamard (fun x=>Triangular.dataWire (j x)) hj).append
    (OpsEmits.cleanPermutation (translateForward hR hb hb) (translateBackward hR hb hb) (hb.unaryAdd hb)
      (fun x=>Triangular.translation_count_forward (j x)) (fun x=>Triangular.translation_count_backward (j x)))
lemma triPrefix_eq (b k : ℕ) (h : k≤b) :
    Triangular.triPrefix b k h=(List.ofFn (fun i:Fin k=>Triangular.rowCircuit (i.castLE h))).flatten:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [Triangular.triPrefix,ih (by omega),List.ofFn_succ',List.concat_eq_append,List.flatten_append]
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
    apply congrArg₂ List.append
    · apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      apply congrArg Triangular.rowCircuit
      apply Fin.ext
      rfl
    · apply congrArg Triangular.rowCircuit
      apply Fin.ext
      rfl
lemma fullPrefix (hb : Emits ea unaryCode b) : OpsEmits ea (fun x=>Triangular.triPrefix (b x) (b x) le_rfl):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σz,Fin (b z)=>(x.2.val,x.1))
  have h:=OpsEmits.concat (p:=fun x (i:Fin (b x))=>Triangular.rowCircuit i) hb (row (hb.comp hx.snd) (fun x:Σz,Fin (b z)=>x.2) hx.fst.unaryNat)
  exact h.congr (by intro x;rw [triPrefix_eq];rfl)
lemma transform (ha : Emits ea unaryCode a) : OpsEmits ea (fun x=>Triangular.transform (a x)):=
  ((preparation ha).append (fullPrefix (ha.unaryAdd (const _ _ 2)))).append (preparation ha).reverse
lemma uniform (hb : Emits ea unaryCode b) : OpsEmits ea (fun x=>Triangular.uniformPreparation (b x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (OpsEmits.hadamards hb (fun _=>le_rfl)).place (fun x=>Triangular.dataRegister (b x))
    (fun _ i=>i) (by intros;rfl) hx.snd
end ExactQuantumFactoring.TriangularEmission

end



end OAI
