import Mathlib
import OAI.Computability.QuantumFactoring.NetworkDependentEmission
import OAI.Computability.QuantumFactoring.CircuitPreparationEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n p q r : α→ℕ}
lemma firstSelect (hp : Emits ea unaryCode p) (hq : Emits ea unaryCode q) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.select (firstRegister (p x) (q x) (r x))):=
  selectSlice ((hp.unaryAdd hq).unaryAdd hr) hp (const _ _ 0) _ (by intros;simp only [Nat.zero_add];rfl)
lemma targetSelect (hp : Emits ea unaryCode p) (hq : Emits ea unaryCode q) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.select (targetRegister (p x) (q x) (r x))):=
  selectSlice ((hp.unaryAdd hq).unaryAdd hr) hq hp.unaryNat _ (by intros;rfl)
lemma zeros (hn : Emits ea unaryCode n) (hp : Emits ea unaryCode p) :
    NetEmits ea (fun x=>Completion.zeros (n x) (p x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (p a)=>(x.2.val,x.1))
  exact vectorOfFn hn hp (constant (hn.comp hx.snd) (const _ _ false))
lemma packNet {a : ∀x,BooleanNetwork (n x) (p x)} {b : ∀x,BooleanNetwork (n x) (q x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hn : Emits ea unaryCode n) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.packNet (r x) (a x) (b x)):=
  (ha.pair hb).pair (zeros hn hr)
end ExactQuantumFactoring.NetworkEmission.NetEmits

namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {p q r : α→ℕ}
lemma appendPrepared {a : ∀x,List (Instruction (p x))} {f : ∀x,BooleanNetwork (p x) (q x)}
    (ha : OpsEmits ea a) (hf : NetworkEmission.NetEmits ea f) (hp : Emits ea unaryCode p)
    (h : ∀x,(f x).net.count≤r x) {b : ∀x,List (Instruction (q x))} (hb : OpsEmits ea b) :
    OpsEmits ea (fun x=>ExactQuantumFactoring.appendPrepared (a x) (f x) (h x) (b x)):=
  (ha.first q r).append (prepared hf hp h hb)
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI
