import Mathlib
import OAI.Computability.QuantumFactoring.NetworkLoopEmission
import OAI.Computability.QuantumFactoring.CircuitProgramEmission
import OAI.Computability.QuantumFactoring.BitStackDependentChoice
import OAI.Computability.QuantumFactoring.Emits

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {k : α→ℕ}
lemma ofFnDep (d : β) {f : ∀x,Fin (k x)→β} (hk : Emits ea unaryCode k)
    (hf : Emits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) eb (fun x=>f x.1 x.2)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (f x)):=by
  let c:=fun x:ℕ×α=>x.1<k x.2
  let g:=fun x i=>if h:i<k x then f x ⟨i,h⟩ else d
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hc:=hx.fst.unaryNat.natLt (hk.comp hx.snd).unaryNat
  have hy : Emits (fun x:{a:ℕ×α // c a}=>prodCode unaryCode ea x.val) eb (fun x=>g x.val.2 x.val.1):=by
    exact (hf.precompose (fun x:{a:ℕ×α // c a}=>(⟨x.val.2,⟨x.val.1,x.property⟩⟩ : Σa,Fin (k a)))).congr
      (by intro x;dsimp only [g];rw [dite_eq_left x.property])
  have hn : Emits (fun x:{a:ℕ×α // ¬c a}=>prodCode unaryCode ea x.val) eb (fun x=>g x.val.2 x.val.1):=by
    exact (const _ _ d).congr (by intro x;dsimp only [g];rw [dite_eq_right x.property])
  obtain ⟨p⟩:=splitOn (f:=fun x:ℕ×α=>g x.2 x.1) c hc hy hn
  exact ((ofProcedure (Procedure.tabulate (f:=g) d p)).comp (hk.pair (id ea))).congr (by
    intro x;rw [←NetworkEmission.ofFn_nat_eq_map];congr 1;funext i;simp only [g,i.isLt,dite_eq_left])
lemma flatten (d : β) {f : α→List (List β)} (hf : Emits ea (listCode (listCode eb)) f) :
    Emits ea (listCode eb) (fun x=>(f x).flatten):=
  (ofProcedure (Procedure.listFlatten eb d)).comp hf
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma concat {p : ∀x,Fin (k x)→List (Instruction (q x))} (hk : Emits ea unaryCode k)
    (hp : OpsEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>p x.1 x.2)) :
    OpsEmits ea (fun x=>(List.ofFn (p x)).flatten):=by
  exact ((ofFnDep (f:=fun x i=>(p x i).map eraseOp) [] hk hp).flatten (⟨plainGate .not,[]⟩ : Op)).congr (by
    intro x;simp only [List.map_flatten,List.map_ofFn];rfl)
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end

end OAI
