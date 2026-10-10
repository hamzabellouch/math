import Mathlib
import OAI.Computability.QuantumFactoring.EmissionBoundedRecursion

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {K : α→ℕ} {F : α→ℕ→β}
lemma stages (hK : Emits ea unaryCode K) (h0 : Emits ea eb (fun x=>F x 0))
    (hs : Emits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode eb) (x.1,(x.2.val,F x.1 x.2.val))) eb
      (fun x=>F x.1 (x.2.val+1)))
    (hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>(eb (F x.1 x.2.val)).length)) :
    Emits ea eb (fun x=>F x (K x)):=by
  let ec:=recursionCode (ea:=ea) (eb:=eb) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode eb))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) eb
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>(⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) eb
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  exact boundedRecursion K F hK h0 (splitOn c htest hy hz) hb
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
