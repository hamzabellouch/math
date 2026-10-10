import Mathlib
import OAI.Computability.QuantumFactoring.DescendingFilterEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma filterStepEmitter {α : Type} {ea : α→List Bool} {k : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : NetEmits (prodCode ea unaryCode) (fun x=>prev x.1 x.2))
    (hc : NetEmits (fun x:Σa,Σs,BooleanNetwork (k a) (w a (s+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2))) (fun x=>keep x.1 x.2.1 x.2.2)) :
    Emits (fun x:Σa,{r:FilterState (k a) (w a) // 0<r.depth}=>prodCode ea filterCode (x.1,x.2.val.code))
      filterCode (fun x=>(filterStep (prev x.1) (keep x.1) x.2.val).code):=by
  let ix:=Σa,Σs,BooleanNetwork (k a) (w a (s+1)) × List (BooleanNetwork (k a) 1)
  let enc:ix→List Bool:=fun x=>prodCode ea filterCode (x.1,(x.2.1+1,erasePack x.2.2.1,x.2.2.2.map erasePack))
  have hx:=(BitStackProgram.Emits.id (prodCode ea filterCode)).precompose
    (fun x:ix=>(x.1,(x.2.1+1,erasePack x.2.2.1,x.2.2.2.map erasePack)))
  have hd: Emits enc unaryCode (fun x=>x.2.1):=
    ((hx.snd.fst.unaryNat.natSub (const _ _ 1)).boundedUnary hx.snd.fst (fun _=>Nat.sub_le _ _)).congr (fun _=>by dsimp only;omega)
  have hp':=hp.compInput (hx.fst.pair hd)
  have hr:=NetEmits.ofCanonical hx.snd.snd.fst
  have hraw:=(hr.comp hp').canonical
  let g:ix→Σa,Σs,BooleanNetwork (k a) (w a (s+1)):=fun x=>⟨x.1,x.2.1,x.2.2.1⟩
  have hk:=hc.canonical.comp ((hx.fst.pair (hd.pair hx.snd.snd.fst)).recode (g:=g) (fun _=>rfl))
  have hs:=hd.pair (hraw.pair (hk.listCons hx.snd.snd.snd))
  let view:(Σa,{r:FilterState (k a) (w a) // 0<r.depth})→ix:=fun x=>⟨x.1,x.2.val.positiveView x.2.property⟩
  have h:=hs.precompose view
  have he : (fun x=>enc (view x))=(fun x:Σa,{r:FilterState (k a) (w a) // 0<r.depth}=>prodCode ea filterCode (x.1,x.2.val.code)):=by
    funext x
    have hv:=x.2.val.positiveView_eq x.2.property
    exact congrArg (fun r=>prodCode ea filterCode (x.1,r.code)) hv
  change Emits (fun x=>enc (view x)) filterCode _ at h
  rw [he] at h
  exact h.congr (by
    intro x
    have hv:=x.2.val.positiveView_eq x.2.property
    exact congrArg (fun r=>(filterStep (prev x.1) (keep x.1) r).code) hv)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
