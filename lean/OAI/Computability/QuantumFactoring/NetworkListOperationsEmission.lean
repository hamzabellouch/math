import Mathlib
import OAI.Computability.QuantumFactoring.NetworkListEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma congrList {f g : ∀x,List (BooleanNetwork (n x) (m x))} (hf : NetsEmits ea f)
    (h : ∀x,f x=g x) : NetsEmits ea g:=hf.congr (fun x=>congrArg (List.map erasePack) (h x))
lemma concat {f : ∀x,Fin (k x)→List (BooleanNetwork (n x) (m x))} (hk : Emits ea unaryCode k)
    (hf : NetsEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetsEmits ea (fun x=>(List.ofFn (f x)).flatten):=by
  exact ((ofFnDep (f:=fun x i=>(f x i).map erasePack) [] hk hf).flatten emptyPack).congr (by
    intro x;simp only [List.map_flatten,List.map_ofFn];rfl)
lemma replicate {f : ∀x,BooleanNetwork (n x) (m x)} (hk : Emits ea unaryCode k) (hf : NetEmits ea f) :
    NetsEmits ea (fun x=>List.replicate (k x) (f x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact (ofFn hk (hf.compInput hx.snd)).congrList (by intro x;exact List.ofFn_const _ _)
lemma map {f : ∀x,List (BooleanNetwork (n x) (m x))} {u v : α→ℕ}
    {g : ∀x,BooleanNetwork (n x) (m x)→BooleanNetwork (u x) (v x)} (hf : NetsEmits ea f)
    (hg : NetEmits (fun x:Σa,Fin ((f a).length)=>prodCode unaryCode ea (x.2.val,x.1))
      (fun x=>g x.1 ((f x.1).get x.2))) : NetsEmits ea (fun x=>(f x).map (g x)):=by
  exact (ofFn (g:=fun x i=>g x ((f x).get i)) hf.length hg).congrList (by
    intro x;conv_rhs=>rw [←List.ofFn_get (f x),List.map_ofFn]
    rfl)
lemma repeated {f : ∀x,List (BooleanNetwork (n x) (m x))} (hk : Emits ea unaryCode k) (hf : NetsEmits ea f) :
    NetsEmits ea (fun x=>(List.replicate (k x) (f x)).flatten):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact (concat (f:=fun x _=>f x) hk (hf.comp hx.snd)).congrList (by intro x;rw [List.ofFn_const])
lemma sequence {f : ∀x,List (BooleanNetwork (n x) (n x))} (hn : Emits ea unaryCode n) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>BooleanNetwork.sequence (f x)):=by
  refine ⟨fun x=>((f x).map erasePack).foldr compPack (identityPack (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.compPackP)).comp
      (hf.pair ((ofProcedure Emission.identityPackP).comp hn)),?_⟩
  intro x
  dsimp only
  generalize f x=l
  induction l with
  | nil=>exact identityPack_value _
  | cons a as ih=>exact compPack_spec _ _ _ _ rfl ih
end NetsEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
