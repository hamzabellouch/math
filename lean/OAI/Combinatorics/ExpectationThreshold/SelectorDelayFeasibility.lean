import OAI.Combinatorics.ExpectationThreshold.SelectorDelay
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Feasibility after delaying one color

Removing a point from a tested prefixSet subtracts exactly its truncated weight
from the excess. If that point is not heavy, the heavy-set condition survives;
the crossing count decreases by one, so the same cutoff remains admissible.
The other tests and their cutoffs are unchanged.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem truncatedExcess_erase (mu : α → ℝ) (A : Finset α) (d u : ℝ)
    (x : α) (hx : x ∈ A) :
    truncatedExcess mu (A.erase x) d u =
      truncatedExcess mu A d u - min (mu x) u := by
  classical
  unfold truncatedExcess
  calc
    (∑ y, min (mu y) u * ((if y ∈ A.erase x then 1 else 0) - (1 - d))) =
        ∑ y, (min (mu y) u * ((if y ∈ A then 1 else 0) - (1 - d)) -
          if y = x then min (mu x) u else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp only [Finset.notMem_erase, ite_false, hx, ite_true]
        ring
      · simp [Finset.mem_erase, hyx]
    _ = (∑ y, min (mu y) u * ((if y ∈ A then 1 else 0) - (1 - d))) -
        min (mu x) u := by
      rw [Finset.sum_sub_distrib]
      simp

/-- The same cutoff works after deleting a non-heavy point and reducing the
crossing parameter by one. No maximality assumption on the cutoff is used. -/
theorem Admissible.erase_one {mu : α → ℝ} {A : Finset α} {m m' d u : ℝ}
    (hu : Admissible mu A m d u) {x : α} (hx : x ∈ A)
    (hxu : mu x ≤ u) (hm : m' + 1 = m) :
    Admissible mu (A.erase x) m' d u := by
  refine ⟨hu.1, hu.2.1, ?_, ?_⟩
  · intro y hy
    refine Finset.mem_erase.mpr ⟨?_, hu.2.2.1 y hy⟩
    intro hyx
    subst y
    exact (not_lt_of_ge hxu) hy
  · rw [truncatedExcess_erase mu A d u x hx]
    calc
      m' * u = m * u - u := by rw [← hm]; ring
      _ ≤ truncatedExcess mu A d u - u := sub_le_sub_right hu.2.2.2 u
      _ ≤ truncatedExcess mu A d u - min (mu x) u :=
        sub_le_sub_left (min_le_right (mu x) u) _

/-- An actual one-step delay preserves all tests for the same family member.
At the affected scale it uses the supplied cutoff; all other cutoffs are the
ones already supplied by `hfeasible`. -/
theorem feasibleFor_delayColor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) (H : ↥F) (hfeasible : FeasibleFor mu a z H)
    (x : α) (i : Fin s) (hx : (z x).val = i.val)
    (hmove : (z x).val < (a x).val) (ε : ℝ)
    (hε : Admissible (mu.weight H) (prefixSet z i)
      (crossings a z i : ℝ) (dscale i) ε)
    (hweight : mu.weight H x ≤ ε) :
    FeasibleFor mu a (delayColor z x i) H := by
  intro j
  by_cases hji : j = i
  · subst j
    refine ⟨ε, ?_⟩
    rw [prefix_delayColor_self z x i hx]
    have hmem : x ∈ prefixSet z i := by simp [prefixSet, hx]
    have hcount : (crossings a (delayColor z x i) i : ℝ) + 1 =
        (crossings a z i : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : ℝ))
          (crossings_delayColor_self a z x i hx hmove)
    exact hε.erase_one hmem hweight hcount
  · obtain ⟨u, hu⟩ := hfeasible j
    refine ⟨u, ?_⟩
    rw [prefix_delayColor_of_ne z x i j hx hji,
      crossings_delayColor_of_ne a z x i j hx hji]
    exact hu

end TalagrandThreshold.Selector

end

end OAI
