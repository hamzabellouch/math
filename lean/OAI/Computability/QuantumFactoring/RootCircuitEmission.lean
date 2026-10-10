import Mathlib
import OAI.Computability.QuantumFactoring.NetworkModularEmission
import OAI.Computability.QuantumFactoring.NetworkSequenceEmission
import OAI.Computability.QuantumFactoring.BitStackPowers

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {w e k : α→ℕ}
lemma rootModulus (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.rootModulus (w x)):=
  selectSlice (hw.unaryAdd hw) hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma rootGuess (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.rootGuess (w x)):=
  selectSlice (hw.unaryAdd hw) hw hw.unaryNat _ (by intros;rfl)
lemma staticPower (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>BitArithmetic.staticPower (w x) (e x)):=by
  have hs:=((rootModulus hw).pair (mul hw)).iterate (hw.unaryAdd hw) he
  exact ((identity hw).pair (wordConst hw hw (const _ _ 1))).comp
    (hs.rewireSlice hw hw.unaryNat _ (by intros;rfl))
lemma rootNext (hw : Emits ea unaryCode w) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.rootNext (w x) (k x)):=by
  have h2 : Emits ea Nat.bits (fun x=>2^(k x)):=
    (ofProcedure Procedure.binaryPow).comp (hk.pair (const _ _ 2))
  exact ((rootGuess hw).pair (wordConst (hw.unaryAdd hw) hw h2)).comp (add hw)
lemma rootStep (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.rootStep (w x) (e x) (k x)):=by
  have hn:=rootNext hw hk
  have hg:=rootGuess hw
  have hm:=rootModulus hw
  exact hm.pair (wordMux ((hn.comp (staticPower hw he)).wordLe hm hw) hn hg hw)
end NetEmits
lemma rootPrefix_emission : NetEmits (prodCode unaryCode (prodCode unaryCode unaryCode))
    (fun x=>rootPrefix x.2.1 x.2.2 x.1):=by
  let ea:=prodCode unaryCode (prodCode unaryCode unaryCode)
  have hx:=BitStackProgram.Emits.id ea
  have hk:=hx.fst
  have hw:=hx.snd.fst
  have he:=hx.snd.snd
  have hj:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  obtain ⟨p,hp,ep⟩:=NetEmits.rootStep (hw.comp hj.snd) (he.comp hj.snd) hj.fst
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=fun x i=>p (i,x)) emptyPack pp)).comp (hk.pair hx)
  let q:=fun x j=>((List.range j).map (fun i=>p (i,x))).foldl (fun a b=>compPack b a) (identityPack (x.2.1+x.2.1))
  have hq : Emits ea packCode (fun x=>q x x.1):=
    (ofProcedure Emission.foldReverseCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp (hw.unaryAdd hw)))
  refine ⟨fun x=>q x x.1,hq,?_⟩
  intro x
  suffices ∀j,(q x j).val.value=erase (rootPrefix x.2.1 x.2.2 j) from this x.1
  intro j
  induction j with
  | zero=>exact identityPack_value _
  | succ j ih=>
    dsimp only [q]
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
    exact compPack_spec _ _ _ _ (ep (j,x)) ih
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n e : α→ℕ}
lemma rootPrefix {w k : α→ℕ} (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) (hk : Emits ea unaryCode k) :
    NetEmits ea (fun x=>BitArithmetic.rootPrefix (w x) (e x) (k x)):=
  rootPrefix_emission.input (hk.pair (hw.pair he))
lemma boundedRoot (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>boundedRootNet (n x) (e x)):=by
  have hw:=(hn.unaryMul hn).unarySucc
  exact ((identity hw).pair (wordConst hw hw (const _ _ 0))).comp
    ((rootPrefix hw he hn).rewireSlice hw hw.unaryNat _ (by intros;rfl))
lemma rootCheck {w : α→ℕ} (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>BitArithmetic.rootCheck (w x) (e x)):=by
  have hg:=rootGuess hw
  exact ((wordConst (hw.unaryAdd hw) hw (const _ _ 2)).wordLe hg hw).band
    ((hg.comp (staticPower hw he)).equalOn (rootModulus hw) hw)
lemma exponentCheck (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e) :
    NetEmits ea (fun x=>BitArithmetic.exponentCheck (n x) (e x)):=by
  have hw:=(hn.unaryMul hn).unarySucc
  exact ((identity hw).pair (boundedRoot hn he)).comp (rootCheck hw he)
lemma perfectPower (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>perfectPowerNet (n x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hN:=hn.comp hx.snd
  have hE:=hx.fst
  have hc:=(hE.unaryNat.natLt (const _ _ 2)).boolNot
  have hf:=ite hc (exponentCheck hN hE) (constant (hN.unaryMul hN).unarySucc (const _ _ false))
  exact (anyRange (f:=fun x i=>if !(decide (i<2)) then BitArithmetic.exponentCheck (n x) i else BooleanNetwork.constant false) (hn.unaryMul hn).unarySucc hf hn.unarySucc).congr (by
    intro x;unfold perfectPowerNet;congr 1;apply congrArg List.ofFn;funext i
    simp only [Bool.not_eq_true',decide_eq_false_iff_not,not_lt])
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
