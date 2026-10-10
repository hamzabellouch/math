import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryGuard

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
noncomputable def dependentIfTotal (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a)))
    (f : (a : α) → ¬p a → β) (g : (a : α) → p a → β)
    (F : PolyProgram (fun a : {a // ¬p a} => ea a.val) eb (fun a => f a.val a.property))
    (G : PolyProgram (fun a : {a // p a} => ea a.val) eb (fun a => g a.val a.property)) :
    PolyProgram ea eb (fun a => if h : p a then g a h else f a h) := by
  classical
  by_cases h0 : Nonempty {a // ¬p a}
  · by_cases h1 : Nonempty {a // p a}
    · exact dependentIf p P f g F G h0.some h1.some
    · have h : ∀a, ¬p a := fun a ha => h1 ⟨⟨a,ha⟩⟩
      exact F.recode (fun a => ⟨a,h a⟩) (fun _ => rfl) (fun a => by simp only [dite_eq_right (h a)])
  · have h : ∀a, p a := fun a => by by_contra ha; exact h0 ⟨⟨a,ha⟩⟩
    exact G.recode (fun a => ⟨a,h a⟩) (fun _ => rfl) (fun a => by simp only [dite_eq_left (h a)])
end MetricKMedian.Binary.PolyProgram
end

end OAI
