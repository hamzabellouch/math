import Mathlib.Tactic

namespace OAI

/-!
# Parity growth in the breadth-first layers

These are the two numerical contradictions in the proof of manuscript
Proposition `clq:layer-interface`. The function `p` records alternating
layer independence sums, whose growth contradicts their global bound.
-/

namespace CycleClique.Construction
/-- The even-parameter layer inequalities force too much parity growth. -/
theorem even_layer_growth_contradiction {s : ℕ} (_hs : 1 ≤ s) (p : ℕ → ℕ)
    (hzero : p 0 = 1) (hbound : p s ≤ 2 * s)
    (hstep : ∀ i < s,
      2 * s * p i < s * (p (i + 1) + p i - 1)) : False := by
  have hgrowth : ∀ i ≤ s, 1 + 2 * i ≤ p i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro his
      have hprev := ih (by omega)
      have hineq := hstep i (by omega)
      have hsum : p (i + 1) + p i - 1 + 1 = p (i + 1) + p i :=
        Nat.sub_add_cancel (by omega)
      have hincrement : p i + 2 ≤ p (i + 1) := by nlinarith
      omega
  have := hgrowth s le_rfl
  omega

/-- In the odd case the final increment is at least three, rather
than the usual two. -/
theorem odd_layer_growth_contradiction {s : ℕ} (hs : 2 ≤ s) (p : ℕ → ℕ)
    (hzero : p 0 = 1) (hbound : p s ≤ 2 * s + 1)
    (hstep : ∀ i < s,
      (2 * s + 1) * p i ≤ s * (p (i + 1) + p i - 1)) : False := by
  have hgrowth : ∀ i ≤ s, 1 + 2 * i ≤ p i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro his
      have hprev := ih (by omega)
      have hineq := hstep i (by omega)
      have hsum : p (i + 1) + p i - 1 + 1 = p (i + 1) + p i :=
        Nat.sub_add_cancel (by omega)
      have hincrement : p i + 2 ≤ p (i + 1) := by nlinarith
      omega
  have hprev := hgrowth (s - 1) (by omega)
  have hineq := hstep (s - 1) (by omega)
  have hindex : s - 1 + 1 = s := by omega
  rw [hindex] at hineq
  have hsum : p s + p (s - 1) - 1 + 1 = p s + p (s - 1) :=
    Nat.sub_add_cancel (by omega)
  have hincrement : p (s - 1) + 3 ≤ p s := by nlinarith
  omega

end CycleClique.Construction

end OAI
