import Mathlib
import OAI.Computability.QuantumFactoring.TableFavorableCount
import OAI.Computability.QuantumFactoring.ComponentLevelEmission
import OAI.Computability.QuantumFactoring.DistinctProductEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n t K : α→ℕ}
lemma sumOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.sumNet (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=add hn
  obtain ⟨b,hb,eb⟩:=wordConst hk hn (const _ _ 0)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (k x) (n x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (BitArithmetic.sumNet (List.ofFn g)):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,BitArithmetic.sumNet,BitVec.ofNat_eq_ofNat] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,List.ofFn_succ,BitArithmetic.sumNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
lemma tableLevel {m : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t)
    (hm : NetEmits ea m) (hps : NetsEmits ea ps) : NetEmits ea (fun x=>BitArithmetic.tableLevelNet (m x) (ps x) (t x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  have hv:=componentLevel (hk.comp hx.snd) (hn.comp hx.snd) (ht.comp hx.snd) (hm.compInput hx.snd) hps.get
  exact (distinctProductOfFn (f:=fun x i=>(ps x).get i) (value:=fun x p=>BitArithmetic.componentLevelNet (m x) p (t x)) hk hn hps.length hps.get hv).congr
    (by intro x;rw [List.ofFn_get];rfl)
lemma tableBadCount {m : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hps : NetsEmits ea ps) :
    NetEmits ea (fun x=>BitArithmetic.tableBadCountNet (m x) (ps x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a+1)=>(x.2.val,x.1))
  exact sumOfFn hk hn hn.unarySucc (tableLevel (hk.comp hx.snd) (hn.comp hx.snd) hx.fst (hm.compInput hx.snd) (hps.comp hx.snd))
lemma tableFavorableCount {m : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hps : NetsEmits ea ps) :
    NetEmits ea (fun x=>BitArithmetic.tableFavorableCountNet (m x) (ps x)):=
  natSubOn hk hn (primesPhi hk hn hm hps) (tableBadCount hk hn hm hps)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
