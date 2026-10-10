import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanProducts
import OAI.Combinatorics.KMedian.Binary.BooleanFinite
import OAI.Combinatorics.KMedian.Binary.BooleanRecode

namespace OAI


                                   
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

def checked (p : α → Prop) [DecidablePred p] (a0 : {a // p a}) (a : α) : {a // p a} :=
  if h : p a then ⟨a,h⟩ else a0

noncomputable def checkedProgram (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a))) (a0 : {a // p a}) :
    PolyProgram ea (fun a : {a // p a} => ea a.val) (checked p a0) := by
  let raw : PolyProgram ea id ea := (identity ea).recode id (fun _ => rfl) (fun _ => rfl)
  let q := ite P (constant ea id (ea a0.val)) raw
  exact q.recode id (fun _ => rfl) (fun a => by
    by_cases h : p a
    · simp [checked,h]
    · simp [checked,h])

noncomputable def dependentIf (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a)))
    (f : (a : α) → ¬p a → β) (g : (a : α) → p a → β)
    (F : PolyProgram (fun a : {a // ¬p a} => ea a.val) eb (fun a => f a.val a.property))
    (G : PolyProgram (fun a : {a // p a} => ea a.val) eb (fun a => g a.val a.property))
    (a0 : {a // ¬p a}) (a1 : {a // p a}) :
    PolyProgram ea eb (fun a => if h : p a then g a h else f a h) := by
  let notP := (P.comp boolNot).congr (fun a => decide (¬p a)) (fun a => by simp [Function.comp_apply])
  let FF := (checkedProgram (fun a => ¬p a) notP a0).comp F
  let GG := (checkedProgram p P a1).comp G
  exact (ite P FF GG).congr _ (fun a => by
    by_cases h : p a
    · simp [Function.comp_apply,checked,h]
    · simp [Function.comp_apply,checked,h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
