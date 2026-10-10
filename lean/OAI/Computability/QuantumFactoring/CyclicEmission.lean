import Mathlib
import OAI.Computability.QuantumFactoring.ModularSumEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w : α→ℕ}
lemma cyclicMul {a b : ∀x,BooleanNetwork (n x) (s x*w x)}
    {m : ∀x,BooleanNetwork (n x) (w x)} [∀x,NeZero (s x)]
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>cyclicMulNet (a x) (b x) (m x)):=by
  apply wordBlocks hn hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  apply sumModOfFn (hn.comp hx.snd) (hw.comp hx.snd) (hs.comp hx.snd) (hm.input hx.snd)
  have hy:=(BitStackProgram.Emits.id (prodCode unaryCode (fun x:Σa,Fin (s a)=>prodCode unaryCode ea (x.2.val,x.1)))).precompose
    (fun x:Σa:Σa,Fin (s a),Fin (s a.1)=>(x.2.val,x.1))
  have ho:=hx.snd.comp hy.snd
  have hS:=hs.comp ho
  have hW:=hw.comp ho
  have hi:=hy.fst.unaryNat
  have hk:=hx.fst.comp hy.snd
  have hj:=((hS.unaryNat.natSub hi).natAdd hk.unaryNat).natMod hS.unaryNat
  have hleft:=blockNet hS hW (fun x=>x.2) hi
  have hright:=blockNet hS hW (fun x=>x.1.2-x.2) hj
  exact mulMod ((ha.input ho).comp hleft) ((hb.input ho).comp hright) (hm.input ho) hW
lemma cyclicOne (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s)
    (hw : Emits ea unaryCode w) [∀x,NeZero (s x)] :
    NetEmits ea (fun x=>BitArithmetic.cyclicOne (n:=n x) (s x) (w x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hc:=hx.fst.unaryNat.natEq (const _ _ 0)
  apply arrayConstant hn hs hw
  exact (hc.ite (const _ _ 1) (const _ _ 0)).congr (by intro x;simp only [Fin.ext_iff,Fin.val_zero,decide_eq_true_eq])
lemma cyclicAdd {a b : ∀x,BooleanNetwork (n x) (s x*w x)}
    {m : ∀x,BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>cyclicAddNet (a x) (b x) (m x)):=by
  apply wordBlocks hn hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hp:=blockNet (hs.comp hx.snd) (hw.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
  exact addMod ((ha.input hx.snd).comp hp) ((hb.input hx.snd).comp hp) (hm.input hx.snd) (hw.comp hx.snd)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
