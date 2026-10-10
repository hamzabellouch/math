import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialScalar
import OAI.Analysis.MatrixSigning.Complexity.PolynomialStored
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies

namespace OAI

section
namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
  {f : α → β} {g : β → γ}
lemma PolyTime.then {r : Realizes ea eb f} {s : Realizes eb ec g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.then s) := @poly_then _ _ _ _ _ _ _ _ _ _ hr hs
lemma PolyTime.both {g : α → γ} {r : Realizes ea eb f} {s : Realizes ea ec g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.both s) := @poly_both _ _ _ _ _ _ _ _ _ _ hr hs
lemma PolyTime.congr {g : α → β} {r : Realizes ea eb f} (hr : PolyTime r)
    (h : ∀x,f x=g x) : PolyTime (r.congr h) := @poly_congr _ _ _ _ _ _ _ _ hr
lemma PolyTime.changeOutput {ed : δ → Word} {r : Realizes ea eb f} (hr : PolyTime r)
    (g : α → δ) (h : ∀x,eb (f x)=ed (g x)) : PolyTime (r.changeOutput ed g h) := @poly_changeOutput _ _ _ _ _ _ _ _ _ _ hr
lemma PolyTime.ite {p : α → Bool} {g : α → β} {b : Realizes ea boolCode p}
    {r : Realizes ea eb f} {s : Realizes ea eb g} (hb : PolyTime b) (hr : PolyTime r) (hs : PolyTime s) :
    PolyTime (b.ite r s) := @poly_ite _ _ _ _ _ _ _ _ _ _ hb hr hs
lemma runsPolyOf {ι : Type*} {L : ι → ℕ} {r : Realizes ea eb f} (h : PolyTime r) (a : ι → α)
    (ha : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := @RunsPoly.of_poly _ _ _ _ _ _ _ r h a ha
lemma PolyTime.mul {f g : α → ℚ} {r : Realizes ea ratCode f} {s : Realizes ea ratCode g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.mul s) := by
  let := hr;let := hs;exact poly_mul r s
lemma PolyTime.pow {f : α → ℚ} {r : Realizes ea ratCode f}
    (hr : PolyTime r) (n : ℕ) : PolyTime (r.pow n) := by
  let := hr;exact poly_pow r n
end CurrentKS.Realization

end

end OAI
