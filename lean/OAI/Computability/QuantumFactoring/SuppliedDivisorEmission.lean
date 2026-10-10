import Mathlib
import OAI.Computability.QuantumFactoring.FirstProperEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n e K : α→ℕ}
lemma rootOn {m : ∀x,BooleanNetwork (k x) (n x+1)}
    (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>BitArithmetic.rootOn (n x) (e x) (m x)):=by
  have hr:=(hn.unaryMul hn).unarySucc
  exact ((hm.comp (resize hn.unarySucc hr)).comp (boundedRoot hn he)).comp (resize hr hn.unarySucc)
lemma rootsOn {m : ∀x,BooleanNetwork (k x) (n x+1)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hm : NetEmits ea m) :
    NetEmits ea (fun x=>BitArithmetic.rootsOn (n x) (m x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a+1)=>(x.2.val,x.1))
  have hf:=rootOn (hn.comp hx.snd) hx.fst (hm.compInput hx.snd)
  have h:=firstProper (f:=fun x i=>BitArithmetic.rootOn (n x) i.val (m x)) hk hn.unarySucc hn.unarySucc hm hf
  refine h.congr ?_
  intro x
  unfold BitArithmetic.rootsOn
  congr 1
  exact ofFn_nat_eq_map (n x+1) (fun i=>BitArithmetic.rootOn (n x) i (m x))
lemma ordersBits {w : α→ℕ} {m : ∀x,BooleanNetwork (k x) (w x)}
    {a : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {r : ∀x,Fin (K x)→BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (he : Emits ea unaryCode e)
    (hK : Emits ea unaryCode K) (hm : NetEmits ea m)
    (ha : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>a x.1 x.2))
    (hr : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>r x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ordersBits (m x) (List.ofFn (fun i=>(a x i,r x i)))):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σb,Fin (K b)=>(x.2.val,x.1))
  have hf:=candidateBits (hk.comp hx.snd) (hw.comp hx.snd) (he.comp hx.snd) ha (hm.compInput hx.snd) hr
  convert firstProper (f:=fun x i=>BitArithmetic.candidateBits (a x i) (m x) (r x i)) hk hw hK hm hf using 1
  funext x
  simp only [BitArithmetic.ordersBits,List.map_ofFn,Function.comp_def]
lemma suppliedBits {m : ∀x,BooleanNetwork (k x) (n x+1)}
    {a : ∀x,Fin (K x)→BooleanNetwork (k x) (n x+1)}
    {r : ∀x,Fin (K x)→BooleanNetwork (k x) (e x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (he : Emits ea unaryCode e)
    (hK : Emits ea unaryCode K) (hm : NetEmits ea m)
    (ha : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>a x.1 x.2))
    (hr : NetEmits (fun x:Σb,Fin (K b)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>r x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.suppliedBits (n x) (m x) (List.ofFn (fun i=>(a x i,r x i)))):=by
  have roots:=rootsOn hk hn hm
  exact (evenOn hk hn.unarySucc hm).wordMux (wordConst hk hn.unarySucc (const _ _ 2))
    ((properOn hk hn.unarySucc hm roots).wordMux roots (ordersBits hk hn.unarySucc he hK hm ha hr) hn.unarySucc) hn.unarySucc
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
