import OAI.Computability.MatchingCount.SequenceRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α β γ δ : Type} [Coding α] [Coding β] [Coding γ] [Coding δ]

theorem reindex {f : α → β} (hf : Poly f) (g : γ → δ) (i : γ → α)
    (hin : ∀ x,encode x=encode (i x))
    (hout : ∀ x,encode (f (i x))=encode (g x)) : Poly g :=
  ⟨hf.routine.reindex encode encode g i (fun x => (hin x).symm) hout⟩

theorem iterateFrom (step : α → α) (hs : Poly step) (count : β → ℕ) (initial : β → α)
    (hc : Poly count) (hi : Poly initial) (P : Polynomial ℕ)
    (hb : ∀ b j,j≤count b → (encode (step^[j] (initial b))).length≤
      P.eval (encode (count b,initial b)).length) :
    Poly (fun b => step^[count b] (initial b)) := by
  let paired := (pair count initial hc hi).routine
  let setup : Routine encode (fun b => encode (count b,initial b)) (id : β → β) :=
    paired.reindex encode (fun b => encode (count b,initial b)) id id
      (fun _ => rfl) (fun _ => rfl)
  exact ⟨setup.comp (hs.routine.boundedIterate count initial P hb)⟩

end Poly
end BinaryMatching.StackCode
end

end OAI
