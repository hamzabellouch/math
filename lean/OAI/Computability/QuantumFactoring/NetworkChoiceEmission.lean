import Mathlib
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
lemma recodeChoice {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→β} {g : α→γ} (hf : Emits ea eb f) (h : ∀x,eb (f x)=ec (g x)) : Emits ea ec g:=by
  obtain ⟨p⟩:=hf
  exact ⟨p.result h⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
