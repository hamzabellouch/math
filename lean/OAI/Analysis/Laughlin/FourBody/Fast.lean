import Mathlib.Tactic.Ring
import OAI.Analysis.Laughlin.FourBody.Basic

namespace OAI

namespace Laughlin.Certificate

def yEntryFast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℚ :=
  let (p,j,a) := e
  let (q,l,b) := f
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  if D ≤ T then
    let vr := V r D T p j k
    let vs := V s D T q l i
    if vr = 0 ∨ vs = 0 then 0 else
      ((a*b*vr*vs*(i.factorial : ℤ)*(k.factorial : ℤ)*(t.factorial : ℤ) : ℤ) : ℚ) *
        (2 : ℚ) ^ (1-2*(T : ℤ)+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r+s)/2 : ℕ)) /
        ((T-D).factorial : ℚ)
  else 0

theorem yEntry_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntry D r s t e f = yEntryFast D r s t e f := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp [yEntry, yEntryFast]
  split_ifs with hD hz
  · rcases hz with hz | hz <;> simp [hz]
  · push_cast
    ring
  · rfl

def yRowFast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => yEntryFast D r s row.1 e f)).sum)).sum

theorem yRow_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRow D r s row = yRowFast D r s row := by
  simp only [yRow, yRowFast, yEntry_eq_fast]

end Laughlin.Certificate

end OAI
