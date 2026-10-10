import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedFill

namespace OAI

/-! # Conditional prepaid snapshots

The caller charges its fixed control overhead; this stage reserves only the
snapshot allowance, and never clones a cursor after a failed comparison.
-/

namespace LowSpaceSubsetSum.BudgetedSnapshot

universe u
variable {σ : Type u}

def execute (charge : ℕ) (clone : σ → σ × ℕ) (needed : Bool) (s : σ) (budget : ℕ) :
    Option (σ × ℕ) × ℕ :=
  if needed then
    if charge ≤ budget then
      let out := clone s
      (some (out.1, budget - charge), out.2)
    else (none, 1)
  else (some (s, budget), 0)

theorem value (charge : ℕ) (clone : σ → σ × ℕ) (needed : Bool) (s : σ) (budget : ℕ)
    (out : σ) (left : ℕ) (h : (execute charge clone needed s budget).1 = some (out, left)) :
    out = (if needed then (clone s).1 else s) ∧ left ≤ budget := by
  rw [execute] at h
  split at h
  next hn =>
    split at h
    next hb => cases h; exact ⟨by simp only [hn, ↓reduceIte], Nat.sub_le _ _⟩
    next _ => contradiction
  next hn => cases h; exact ⟨by simp only [hn, Bool.false_eq_true, ↓reduceIte], le_rfl⟩

theorem work (charge : ℕ) (clone : σ → σ × ℕ) (hc : ∀ s, (clone s).2 ≤ charge)
    (needed : Bool) (s : σ) (budget : ℕ) :
    (execute charge clone needed s budget).2 ≤ budget + 1 := by
  have hs := hc s
  rw [execute]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

theorem spent (charge : ℕ) (clone : σ → σ × ℕ) (hc : ∀ s, (clone s).2 ≤ charge)
    (needed : Bool) (s : σ) (budget : ℕ) (out : σ) (left : ℕ)
    (h : (execute charge clone needed s budget).1 = some (out, left)) :
    (execute charge clone needed s budget).2 ≤ budget - left := by
  have hs := hc s
  rw [execute] at h ⊢
  split at h
  next hn =>
    simp only [hn, ↓reduceIte]
    split at h
    next hb => simp only [hb, ↓reduceIte]; cases h; omega
    next _ => contradiction
  next hn => simp only [hn, Bool.false_eq_true, ↓reduceIte]; cases h; omega

theorem complete (charge : ℕ) (clone : σ → σ × ℕ) (needed : Bool) (s : σ) (budget : ℕ)
    (hb : (if needed then charge else 0) ≤ budget) :
    ∃ left, (execute charge clone needed s budget).1 =
      some ((if needed then (clone s).1 else s), left) ∧
      budget ≤ left + (if needed then charge else 0) := by
  cases needed
  · exact ⟨budget, rfl, by omega⟩
  · change charge ≤ budget at hb
    exact ⟨budget - charge, by simp only [execute, ↓reduceIte, hb], by simp only [↓reduceIte]; omega⟩

theorem remaining (charge : ℕ) (clone : σ → σ × ℕ) (needed : Bool) (s : σ) (budget : ℕ)
    (out : σ) (left : ℕ) (h : (execute charge clone needed s budget).1 = some (out, left)) :
    budget ≤ left + (if needed then charge else 0) := by
  rw [execute] at h
  split at h
  next hn =>
    split at h
    next hb => cases h; simp only [hn, ↓reduceIte]; omega
    next _ => contradiction
  next hn => cases h; simp only [hn, Bool.false_eq_true, ↓reduceIte]; omega

end LowSpaceSubsetSum.BudgetedSnapshot

end OAI
