import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifierEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
abbrev NetsEmits {α : Type} (ea : α→List Bool) {n m : α→ℕ}
    (f : ∀x,List (BooleanNetwork (n x) (m x))) : Prop:=
  Emits ea (listCode packCode) (fun x=>(f x).map erasePack)
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {n m K : α→ℕ} {f : ∀x,List (BooleanNetwork (n x) (m x))}
lemma ofFn {g : ∀x,Fin (K x)→BooleanNetwork (n x) (m x)} (hK : Emits ea unaryCode K)
    (hg : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>g x.1 x.2)) :
    NetsEmits ea (fun x=>List.ofFn (g x)):=by
  exact (ofFnDep emptyPack hK hg.canonical).congr (fun x=>by rw [List.map_ofFn])
lemma length (hf : NetsEmits ea f) : Emits ea unaryCode (fun x=>(f x).length):=by
  exact ((ofProcedure (NativeAIG.Emission.listUnaryLength packCode emptyPack)).comp hf).congr (by intro x;exact List.length_map ..)
lemma get (hf : NetsEmits ea f) : NetEmits
    (fun x:Σa,Fin ((f a).length)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>(f x.1).get x.2):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((f a).length)=>(x.2.val,x.1))
  have h:=(ofProcedure (Procedure.listGet packCode emptyPack)).comp (hx.fst.unaryNat.pair (hf.comp hx.snd))
  apply NetEmits.ofCanonical
  exact h.congr (by
    intro x
    simp only [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,List.getElem?_eq_getElem x.2.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem])
lemma product (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>BitArithmetic.productNet (f x)):=by
  exact (NetEmits.productOfFn hn hm hf.length hf.get).congr (by intro x;rw [List.ofFn_get])
end NetsEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
