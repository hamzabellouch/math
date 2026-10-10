import Mathlib
import OAI.Computability.QuantumFactoring.EmissionBoundedRecursion
import OAI.Computability.QuantumFactoring.NetworkCanonicalEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {K : α→ℕ} {n m : α→ℕ→ℕ}
    {f : ∀x j,BooleanNetwork (n x j) (m x j)}
/-- Saturation makes the loop's intermediate-state bound valid for every
possible invocation, not merely for the one starting at stage zero. -/
lemma boundedStages (hK : Emits ea unaryCode K)
    (h0 : NetEmits ea (fun x=>f x 0))
    (hs : NetEmits
      (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
        (x.1,(x.2.val,erasePack (f x.1 x.2.val))))
      (fun x=>f x.1 (x.2.val+1)))
    (hn : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>n x.1 x.2.val))
    (hm : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>m x.1 x.2.val))
    (hc : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>f x.1 x.2.val)) :
    NetEmits ea (fun x=>f x (K x)):=by
  let F:=fun x j=>erasePack (f x j)
  let ec:=recursionCode (ea:=ea) (eb:=packCode) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) packCode
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.canonical.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>
      (⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;dsimp only [F];rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) packCode
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  have ht : Emits ec packCode (fun x=>F x.1 (min (x.2.val+1) (K x.1))):=
    BitStackProgram.Emits.splitOn c htest hy hz
  have hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(packCode (F x.1 x.2.val)).length):=
    ((PolyAt.const _ 104).mul ((((hn.add hc).add hm).add (PolyAt.const _ 1)).pow 2)).of_le
      (fun x=>packCode_bound _)
  exact ofCanonical (BitStackProgram.Emits.boundedRecursion K F hK h0.canonical ht hb)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
