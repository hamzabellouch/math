import Mathlib
import OAI.Computability.QuantumFactoring.ProperDivisorEmission
import OAI.Computability.QuantumFactoring.StackEmission
import OAI.Computability.QuantumFactoring.NetworkFoldChoiceEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k w K : α→ℕ}
lemma productOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.productNet (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=mul hw
  obtain ⟨b,hb,eb⟩:=wordConst hk hw (const _ _ 1)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (k x) (w x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (BitArithmetic.productNet (List.ofFn g)):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,BitArithmetic.productNet,BitVec.ofNat_eq_ofNat] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,List.ofFn_succ,BitArithmetic.productNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
lemma primeOrZero {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.primeOrZero (a x)):=
  (zeroWord hk hw ha).bor (ha.comp (primeWord hw))
lemma paddedPair {a b : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.paddedPair (a x) (b x)):=
  (zeroWord hk hw hb).bor ((zeroWord hk hw ha).bnot.band (ha.wordLe hb hw))
lemma unpadWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.unpadWord (a x)):=
  (zeroWord hk hw ha).wordMux (wordConst hk hw (const _ _ 1)) ha hw
lemma candidateProduct {f : ∀x,Fin (w x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w)
    (hf : NetEmits (fun x:Σa,Fin (w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.candidateProduct (f x)):=by
  apply productOfFn hk (hw.unaryMul hw).unarySucc hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
  have hW:=hw.comp hx.snd
  exact (unpadWord (hk.comp hx.snd) hW hf).comp (resize hW (hW.unaryMul hW).unarySucc)
lemma factorVerifier {N : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (w x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hN : NetEmits ea N)
    (hf : NetEmits (fun x:Σa,Fin (w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.factorVerifierOn (N x) (f x)):=by
  have hp : NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (fun i=>BitArithmetic.primeOrZero (f x i)))):=by
    apply allOfFn hk hw
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
    exact primeOrZero (hk.comp hx.snd) (hw.comp hx.snd) hf
  have ho : NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (fun i:Fin (w x*w x)=>
      let p:=finProdFinEquiv.symm i
      if p.1<p.2 then BitArithmetic.paddedPair (f x p.1) (f x p.2) else BooleanNetwork.constant true))):=by
    apply allOfFn hk (hw.unaryMul hw)
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (w a*w a)=>(x.2.val,x.1))
    have hW:=hw.comp hx.snd
    have hi:=hx.fst.unaryNat.natDiv hW.unaryNat
    have hj:=hx.fst.unaryNat.natMod hW.unaryNat
    have h1:NetEmits (fun x:Σa,Fin (w a*w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 (finProdFinEquiv.symm x.2).1):=by
      have hidx:=hi.boundedUnary hW (fun x=> (finProdFinEquiv.symm x.2).1.isLt.le)
      exact hf.compInput ((hidx.pair hx.snd).result (g:=fun x:Σa,Fin (w a*w a)=>(⟨x.1,(finProdFinEquiv.symm x.2).1⟩ : Σa,Fin (w a))) (by intros;rfl))
    have h2:NetEmits (fun x:Σa,Fin (w a*w a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 (finProdFinEquiv.symm x.2).2):=by
      have hidx:=hj.boundedUnary hW (fun x=> (finProdFinEquiv.symm x.2).2.isLt.le)
      exact hf.compInput ((hidx.pair hx.snd).result (g:=fun x:Σa,Fin (w a*w a)=>(⟨x.1,(finProdFinEquiv.symm x.2).2⟩ : Σa,Fin (w a))) (by intros;rfl))
    exact (NetEmits.ite (hi.natLt hj) (paddedPair (hk.comp hx.snd) hW h1 h2)
      (constant (hk.comp hx.snd) (const _ _ true))).congr (by intro x;simp only [decide_eq_true_eq];rfl)
  exact (hp.band ho).band ((candidateProduct hk hw hf).equalOn (hN.comp (resize hw (hw.unaryMul hw).unarySucc)) (hw.unaryMul hw).unarySucc)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
