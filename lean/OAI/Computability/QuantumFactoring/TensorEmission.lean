import Mathlib
import OAI.Computability.QuantumFactoring.NetworkRecursionEmission
import OAI.Computability.QuantumFactoring.CircuitPreparationEmission
import OAI.Computability.QuantumFactoring.OpsEmits

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma tensorWidth (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k) :
    Emits ea unaryCode (fun x=>ExactQuantumFactoring.tensorWidth (q x) (k x)):=
  (hk.unaryMul hq).congr (fun _=>(tensorWidth_eq _ _).symm)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma tensorWire_val (q K : ℕ) (i : Fin K) (j : Fin q) :
    (tensorWire q K i j).val=q*i.val+j.val:=by
  induction K with
  | zero=>exact Fin.elim0 i
  | succ K ih=>
    refine Fin.cases ?_ (fun i=>?_) i
    · simp only [tensorWire,Fin.cases_zero,Fin.val_castAdd,Fin.val_zero,Nat.mul_zero,Nat.zero_add]
    · simp only [tensorWire,Fin.cases_succ,Fin.val_natAdd,ih,Fin.val_succ,Nat.mul_add,Nat.mul_one];omega
lemma tensorPack_value {n q K : ℕ} (fs : Fin K→BooleanNetwork n q) (ps : Fin K→Pack)
    (h : ∀i,(ps i).val.value=erase (fs i)) :
    ((List.ofFn ps).foldr pairPack (emptyAt n)).val.value=erase (tensorNetwork fs):=by
  induction K with
  | zero=>simp only [List.ofFn_zero,List.foldr_nil,tensorNetwork,emptyAt,selectPack];rw [erase_select];rfl
  | succ K ih=>
    rw [List.ofFn_succ,List.foldr_cons,tensorNetwork]
    exact pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n q k : α→ℕ}
lemma tensorSelect (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k)
    (i : ∀x,Fin (k x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>ExactQuantumFactoring.tensorSelect (q x) (k x) (i x)):=
  selectSlice (hq.tensorWidth hk) hq (hq.unaryNat.natMul hi) _ (fun _ _=>tensorWire_val _ _ _ _)
lemma tensor {f : ∀x,Fin (k x)→BooleanNetwork (n x) (q x)}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>tensorNetwork (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨s,hs,es⟩:=extendPack hk p hp
  obtain ⟨pp⟩:=hs
  have hps:=(ofProcedure (Procedure.tabulate (f:=s) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (s x)).foldr pairPack (emptyAt (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.pairPackP)).comp
      (hps.pair ((ofProcedure Emission.emptyAtP).comp hn)),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact tensorPack_value _ _ (fun i=>by rw [es];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma tensor {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k) :
    OpsEmits ea (fun x=>tensorProgram (p x) (k x)):=by
  apply boundedStages hk (f:=fun x j=>tensorProgram (p x) j)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
      (fun x:Σa,Fin (k a)=>(x.1,(x.2.val,(tensorProgram (p x.1) x.2.val).map eraseOp)))
    exact parallel (hp.comp hx.fst) hx.snd.snd (hq.comp hx.fst)
  · exact ((hq.tensorWidth hk).unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hk.unaryPoly.mul hp.lengthPoly).pull (fun x:Σa,Fin (k a+1)=>x.1)).of_le (by
      intro x;rw [tensorProgram_length];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI
