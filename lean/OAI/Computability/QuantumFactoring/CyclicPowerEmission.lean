import Mathlib
import OAI.Computability.QuantumFactoring.CyclicEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {s w b : α→ℕ} [∀x,NeZero (s x)]
lemma cyclicStep (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b)
    (i : ∀x,Fin (b x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>BitArithmetic.cyclicStep (s x) (w x) (i x)):=by
  have hA:=hs.unaryMul hw
  have hI:=(hA.unaryAdd hw).unaryAdd hb
  have hW:=hI.unaryAdd hA
  have hbase : NetEmits ea (fun x=>cyclicBase (s x) (w x) (b x)):=
    selectSlice hW hA (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hmod : NetEmits ea (fun x=>cyclicMod (s x) (w x) (b x)):=
    selectSlice hW hw hA.unaryNat _ (by intros;simp only [Fin.val_castAdd,Fin.val_natAdd])
  have hacc : NetEmits ea (fun x=>cyclicAcc (s x) (w x) (b x)):=
    selectSlice hW hA hI.unaryNat _ (by intros;simp only [Fin.val_natAdd])
  have hbit : NetEmits ea (fun x=>cyclicBit (s x) (w x) (i x)):=
    bit hW _ ((hA.unaryAdd hw).unaryNat.natAdd hi)
  have hkeep : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.castAdd (s x*w x) : Fin ((s x*w x+w x)+b x)→Fin (cyclicPowerWidth (s x) (w x) (b x)))):=
    selectSlice hW hI (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hsq:=cyclicMul hW hs hw hacc hacc hmod
  have hprod:=cyclicMul hW hs hw hsq hbase hmod
  exact hkeep.pair (wordMux hbit hprod hsq hA)
lemma cyclicPrefix (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.cyclicPrefix (s x) (w x) (b x) (b x) le_rfl):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (b a)=>(x.2.val,x.1))
  obtain ⟨p,hp,ep⟩:=cyclicStep (hs.comp hx.snd) (hw.comp hx.snd) (hb.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
  obtain ⟨q,hq,eq⟩:=extendPack hb p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hb.pair (id ea))
  have hA:=hs.unaryMul hw
  have hW:=((hA.unaryAdd hw).unaryAdd hb).unaryAdd hA
  let Q:=fun x j=>((List.range j).map (q x)).foldl compPack (identityPack (cyclicPowerWidth (s x) (w x) (b x)))
  have hQ : Emits ea packCode (fun x=>Q x (b x)):=
    (ofProcedure Emission.foldCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp hW))
  refine ⟨fun x=>Q x (b x),hQ,?_⟩
  intro x
  suffices ∀j (hj:j≤b x),(Q x j).val.value=erase (BitArithmetic.cyclicPrefix (s x) (w x) (b x) j hj) from this _ le_rfl
  intro j
  induction j with
  | zero=>intro hj;exact identityPack_value _
  | succ j ih=>
    intro hj
    dsimp only [Q]
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
    apply compPack_spec _ _ _ _ (ih (by omega))
    rw [eq x ⟨j,by omega⟩]
    exact ep ⟨x,⟨j,by omega⟩⟩
lemma cyclicPower (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.cyclicPower (s x) (w x) (b x)):=by
  have hA:=hs.unaryMul hw
  have hI:=(hA.unaryAdd hw).unaryAdd hb
  have hstart:=(identity hI).pair (cyclicOne hI hs hw)
  exact hstart.comp ((cyclicPrefix hs hw hb).rewireSlice hA hI.unaryNat _ (by intros;rfl))
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
