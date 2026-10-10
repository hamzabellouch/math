import Mathlib
import OAI.Computability.QuantumFactoring.NetworkIndexedEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w : α→ℕ}
lemma mul (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mul (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.mul (w x),
    (ofProcedure AIGNetworkEmission.Emission.mulPackP).comp hw,fun x=>AIGNetworkEmission.mulPack_value (w x)⟩
lemma mod (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mod (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.remainder (w x),
    (ofProcedure AIGNetworkEmission.Emission.modPackP).comp hw,fun x=>AIGNetworkEmission.modPack_value (w x)⟩
lemma mulMod {a b c : ∀x,BooleanNetwork (n x) (w x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hc : NetEmits ea c)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mulMod (a x) (b x) (c x)):=by
  have hp:=padRight hw hw
  exact (((((ha.comp hp).pair (hb.comp hp)).comp (mul (hw.unaryAdd hw))).pair
    (hc.comp hp)).comp (mod (hw.unaryAdd hw))).rewireSlice hw (const _ _ 0)
      (fun _=>Fin.castAdd _) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma wordMux {c : ∀x,BooleanNetwork (n x) 1} {a b : ∀x,BooleanNetwork (n x) (w x)}
    (hc : NetEmits ea c) (ha : NetEmits ea a) (hb : NetEmits ea b)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordMux (c x) (a x) (b x)):=by
  obtain ⟨p,hp,ep⟩:=hc;obtain ⟨q,hq,eq⟩:=ha;obtain ⟨r,hr,er⟩:=hb
  exact ⟨fun x=>wordMuxPack (w x) (p x) (q x) (r x),
    (ofProcedure Emission.wordMuxPackP).comp (hw.pair (hp.pair (hq.pair hr))),
    fun x=>wordMuxPack_value _ _ _ (c x) (a x) (b x) (ep x) (eq x) (er x)⟩
end NetEmits

open BitArithmetic
lemma powerStep_emission : ∃p : (ℕ×ℕ)→ℕ→Pack,
    Emits (prodCode unaryCode (prodCode unaryCode unaryCode)) packCode (fun x=>p x.2 x.1) ∧
    ∀w b (i : Fin b),(p (w,b) i.val).val.value=erase (powerStep w i):=by
  let ea:=prodCode unaryCode (prodCode unaryCode unaryCode)
  have hx:=BitStackProgram.Emits.id ea
  have hi:=hx.fst
  have hw:=hx.snd.fst
  have hb:=hx.snd.snd
  have hW:=((hw.unaryAdd hw).unaryAdd hb).unaryAdd hw
  have hB : NetEmits ea (fun x=>powerBase x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hM : NetEmits ea (fun x=>powerModulus x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw hw.unaryNat _ (by intros;simp only [Fin.val_castAdd,Fin.val_natAdd])
  have hA : NetEmits ea (fun x=>powerAcc x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw ((hw.unaryAdd hw).unaryAdd hb).unaryNat _ (by intros;simp only [Fin.val_natAdd])
  have hS:=hA.mulMod hA hM hw
  have hP:=hS.mulMod hB hM hw
  have hF : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.castAdd x.2.1 : Fin ((x.2.1+x.2.1)+x.2.2)→Fin (powerWidth x.2.1 x.2.2))):=
    NetEmits.selectSlice hW ((hw.unaryAdd hw).unaryAdd hb) (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  obtain ⟨s,hs,es⟩:=hS
  obtain ⟨q,hq,eq⟩:=hP
  obtain ⟨f,hf,ef⟩:=hF
  let c:=fun x:ℕ×(ℕ×ℕ)=>bitPack (powerWidth x.2.1 x.2.2) ((x.2.1+x.2.1)+x.1)
  have hc : Emits ea packCode c:=(ofProcedure Emission.bitPackP).comp
    (hW.pair ((hw.unaryNat.natAdd hw.unaryNat).natAdd hi.unaryNat))
  let p:=fun wb i=>pairPack (f (i,wb)) (wordMuxPack wb.1 (c (i,wb)) (q (i,wb)) (s (i,wb)))
  refine ⟨p,(ofProcedure Emission.pairPackP).comp (hf.pair
    ((ofProcedure Emission.wordMuxPackP).comp (hw.pair (hc.pair (hq.pair hs))))),?_⟩
  intro w b i
  apply pairPack_spec _ _ _ _ (ef _)
  exact wordMuxPack_value _ _ _ (powerBit w i)
    (mulMod (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b)) (powerBase w b) (powerModulus w b))
    (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b))
    (bitPack_value ((Fin.natAdd (w+w) i).castAdd w)) (eq _) (es _)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
