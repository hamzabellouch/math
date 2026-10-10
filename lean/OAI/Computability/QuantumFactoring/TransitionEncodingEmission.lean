import Mathlib
import OAI.Computability.QuantumFactoring.DescendingFilterEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n K : α→ℕ}
lemma transitionEncode {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>TransitionWords.encodeNet (f x)):=by
  apply vectorOfFn hk (hn.unaryMul (hK.unaryAdd (const _ _ 1)))
  let X:=Σa,Fin (n a*(K a+1))
  let ix:=fun x:X=>finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) x.2)
  let c:=fun x:X=>(ix x).1.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:X=>(x.2.val,x.1))
  have row:=hx.fst.unaryNat.natDiv (hn.comp hx.snd).unaryNat
  have col:=hx.fst.unaryNat.natMod (hn.comp hx.snd).unaryNat
  have hc : Emits (fun x:X=>prodCode unaryCode ea (x.2.val,x.1)) Procedure.boolCode (fun x=>decide (c x)):=
    row.natLt (hK.comp hx.snd).unaryNat
  apply NetEmits.splitOn c hc
  · have hy:=hx.precompose (fun x:{x:X // c x}=>x.val)
    have hp : Emits (fun x:{x:X // c x}=>prodCode unaryCode ea (x.val.2.val,x.val.1))
        (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1))
        (fun x=>(⟨x.val.1,⟨(ix x.val).1.val,x.property⟩⟩ : Σa,Fin (K a))):=by
      exact (((row.precompose (fun x:{x:X // c x}=>x.val)).boundedUnary
        (hK.comp hy.snd) (fun x=>x.property.le)).pair hy.snd).recode (by intro x;rfl)
    have hnf:=hf.compInput hp
    have hsel:=hnf.rewire (fun x (_ : Fin 1)=>(ix x.val).2)
      (((col.precompose (fun x:{x:X // c x}=>x.val)).listCons (const _ _ [])).congr
        (by intro x;simp [ix]))
    exact hsel.congr (by intro x;dsimp only [TransitionWords.encodeNet];rw [dite_eq_left x.property])
  · exact (constant (hk.comp (hx.precompose (fun x:{x:X // ¬c x}=>x.val)).snd) (const _ _ false)).congr
      (by intro x;dsimp only [TransitionWords.encodeNet];rw [dite_eq_right x.property])
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI
