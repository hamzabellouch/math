import Mathlib

namespace OAI

namespace Problem346

/-- Blocks for the first transfer: `none` is x, `some none` is t,
and `some (some j)` is the j-th common product factor. -/
abbrev FirstBlock (m : ℕ) := Option (Option (Fin m))

/-- The slot labels after transferring the first k factors out of the t block. -/
def firstLabel (r m k : ℕ) (p : Fin (r+1) × Fin (r+m)) : FirstBlock m :=
  if p.1 = 0 then
    if h : p.2.val < k ∧ p.2.val < m then some (some ⟨p.2.val, h.2⟩)
    else some none
  else Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) p.2

@[simp] theorem firstLabel_zero_row (r m k : ℕ) (j : Fin (r+m)) :
    firstLabel r m k (0,j) =
      if h : j.val < k ∧ j.val < m then some (some ⟨j.val,h.2⟩) else some none := by
  simp [firstLabel]

@[simp] theorem firstLabel_succ_row (r m k : ℕ) (i : Fin r) (j : Fin (r+m)) :
    firstLabel r m k (i.succ,j) =
      Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j := by
  simp [firstLabel]

@[simp] theorem firstLabel_initial_zero_row (r m : ℕ) (j : Fin (r+m)) :
    firstLabel r m 0 (0,j) = some none := by
  simp

end Problem346

end OAI
