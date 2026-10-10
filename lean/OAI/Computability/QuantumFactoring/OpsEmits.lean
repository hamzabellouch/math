import Mathlib
import OAI.Computability.QuantumFactoring.EmissionBoundedRecursion
import OAI.Computability.QuantumFactoring.EmissionLengthBounds
import OAI.Computability.QuantumFactoring.CircuitRecursionEmission

namespace OAI

section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {K : α→ℕ} {q : α→ℕ→ℕ}
    {f : ∀x j,List (Instruction (q x j))}
lemma lengthPoly {w : α→ℕ} {p : ∀x,List (Instruction (w x))} (hp : OpsEmits ea p) :
    PolyAt (fun x=>(ea x).length) (fun x=>(p x).length):=by
  exact (BitStackProgram.Emits.lengthPoly hp).of_le (fun x=>by
    simpa only [List.length_map] using list_length_le_code opCode ((p x).map eraseOp))
lemma boundedStages (hK : Emits ea unaryCode K)
    (h0 : OpsEmits ea (fun x=>f x 0))
    (hs : OpsEmits
      (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode (listCode opCode))
        (x.1,(x.2.val,(f x.1 x.2.val).map eraseOp)))
      (fun x=>f x.1 (x.2.val+1)))
    (hq : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>q x.1 x.2.val))
    (hl : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>(f x.1 x.2.val).length)) :
    OpsEmits ea (fun x=>f x (K x)):=by
  let F:=fun x j=>(f x j).map eraseOp
  let ec:=recursionCode (ea:=ea) (eb:=listCode opCode) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) (listCode opCode)
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>(⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;dsimp only [F];rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) (listCode opCode)
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  have ht : Emits ec (listCode opCode) (fun x=>F x.1 (min (x.2.val+1) (K x.1))):=
    BitStackProgram.Emits.splitOn c htest hy hz
  have hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(listCode opCode (F x.1 x.2.val)).length):=
    ((hl.mul ((PolyAt.const _ 202).add ((PolyAt.const _ 32).mul hq))).add (PolyAt.const _ 1)).of_le
      (fun x=>opsCode_bound _)
  exact BitStackProgram.Emits.boundedRecursion K F hK h0 ht hb
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
