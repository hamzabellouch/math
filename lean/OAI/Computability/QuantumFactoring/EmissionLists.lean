import Mathlib
import OAI.Computability.QuantumFactoring.BitStackUnary
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma listNil : Emits ea (listCode eb) (fun _=> ([] : List β)):=const _ _ _
lemma listCons {f : α→β} {g : α→List β} (hf : Emits ea eb f) (hg : Emits ea (listCode eb) g) :
    Emits ea (listCode eb) (fun x=>f x::g x):=(ofProcedure (Procedure.listCons eb)).comp (hf.pair hg)
lemma listAppend (b : β) {f g : α→List β} (hf : Emits ea (listCode eb) f) (hg : Emits ea (listCode eb) g) :
    Emits ea (listCode eb) (fun x=>f x++g x):=(ofProcedure (Procedure.listAppend eb b)).comp (hf.pair hg)
lemma ofFn {k : ℕ} {f : α→Fin k→β} (h : ∀i,Emits ea eb (fun x=>f x i)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (f x)):=by
  induction k with
  | zero=>simpa only [List.ofFn_zero] using (listNil (ea:=ea) (eb:=eb))
  | succ k ih=>
    have ht:=ih (f:=fun x i=>f x i.succ) (fun i=>h i.succ)
    exact ((h 0).listCons ht).congr (by intro x;exact List.ofFn_succ.symm)
lemma unaryAdd {f g : α→ℕ} (h : Emits ea unaryCode f) (j : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>f x+g x):=(ofProcedure Procedure.unaryAdd).comp (h.pair j)
lemma unaryMul {f g : α→ℕ} (h : Emits ea unaryCode f) (j : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>f x*g x):=(ofProcedure Procedure.unaryMul).comp (h.pair j)
lemma unarySucc {f : α→ℕ} (h : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>f x+1):=(ofProcedure Procedure.unarySuccessor).comp h
lemma conditional {c : α→Bool} {f g : α→β} (hc : Emits ea boolCode c)
    (hf : Emits ea eb f) (hg : Emits ea eb g) : Emits ea eb (fun x=>if c x then f x else g x):=by
  obtain ⟨p⟩:=hc;obtain ⟨q⟩:=hf;obtain ⟨r⟩:=hg
  exact ⟨Procedure.conditional p q r⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
