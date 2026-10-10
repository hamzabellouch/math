import Mathlib
import OAI.Computability.QuantumFactoring.NetworkSequenceEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {p b : α→ℕ}
lemma sub (hb : Emits ea unaryCode b) : NetEmits ea (fun x=>BitArithmetic.sub (b x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.sub (b x),
    (ofProcedure AIGNetworkEmission.Emission.subPackP).comp hb,fun _=>AIGNetworkEmission.subPack_value _⟩
lemma translateInput {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.addInput (f x)):=
  (selectSlice (hp.unaryAdd hb) hb hp.unaryNat (fun x=>Fin.natAdd (p x)) (by intros;rfl)).pair
    ((selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).comp hf)
lemma translateForward {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.forward (f x)):=
  (selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).pair
    ((translateInput hf hp hb).comp (add hb))
lemma translateBackward {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.backward (f x)):=
  (selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).pair
    ((translateInput hf hp hb).comp (sub hb))
lemma triangularRow (hb : Emits ea unaryCode b) (j : ∀x,Fin (b x))
    (hj : Emits ea Nat.bits (fun x=>(j x).val)) : NetEmits ea (fun x=>Triangular.rowNetwork (j x)):=by
  let f : α→ℕ→Pack:=fun x i=>if (j x).val ≤ i ∧ i<b x-1 then
    bandPack (bitPack (b x) ((b x-1+(j x).val-i)%b x)) (bitPack (b x) (j x).val)
    else constantPack (b x) false
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hn:=hb.comp hx.snd
  have hi:=hx.fst.unaryNat
  have hJ:=hj.comp hx.snd
  have hB:=hn.unaryNat.natSub (const _ _ 1)
  have hc:=((hi.natLt hJ).boolNot).boolAnd (hi.natLt hB)
  have hr:=((hB.natAdd hJ).natSub hi).natMod hn.unaryNat
  have hA:=(ofProcedure Emission.bitPackP).comp (hn.pair hr)
  have hD:=(ofProcedure Emission.bitPackP).comp (hn.pair hJ)
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>f x.2 x.1):=by
    exact (hc.ite ((ofProcedure Emission.bandPackP).comp (hA.pair hD))
      ((ofProcedure Emission.constantPackP).comp (hn.pair (const _ _ false)))).congr (by
        intro x;simp only [f,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,not_lt,decide_eq_true_eq])
  apply vectorIndexed hb hb f hp
  intro x i
  dsimp only [f,Triangular.rowNetwork]
  split
  · exact bandPack_value _ _ _ _ (bitPack_value (Triangular.rowIndex (j x) i)) (bitPack_value (j x))
  · exact constantPack_value _ _
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
