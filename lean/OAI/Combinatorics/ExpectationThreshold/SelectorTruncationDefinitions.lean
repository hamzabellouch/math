import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Finite weighted truncation

The heavy set uses a strict cutoff. Weights equal to the cutoff are already
saturated when the cutoff increases, as required by the maximal truncation
argument.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The points whose weight is strictly above the cutoff. -/
noncomputable def heavySet (w : α → ℝ) (u : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => u < w x)

/-- The excess mass after every coordinate is truncated at the same cutoff. -/
noncomputable def truncatedExcess (w : α → ℝ) (A : Finset α) (d u : ℝ) : ℝ :=
  ∑ x, min (w x) u * ((if x ∈ A then 1 else 0) - (1 - d))

/-- An admissible cutoff includes all heavy points and meets the truncated
weighted-excess test. -/
def Admissible (w : α → ℝ) (A : Finset α) (m d u : ℝ) : Prop :=
  0 ≤ u ∧ u ≤ 1 ∧ (∀ x, u < w x → x ∈ A) ∧
    m * u ≤ truncatedExcess w A d u

omit [DecidableEq α] in
@[simp] theorem mem_heavySet {w : α → ℝ} {u : ℝ} {x : α} :
    x ∈ heavySet w u ↔ u < w x := by
  classical
  simp [heavySet]

theorem Admissible.heavy_subset {w : α → ℝ} {A : Finset α} {m d u : ℝ}
    (hu : Admissible w A m d u) : heavySet w u ⊆ A := by
  intro x hx
  exact hu.2.2.1 x (mem_heavySet.mp hx)

theorem Admissible.outside_le {w : α → ℝ} {A : Finset α} {m d u : ℝ}
    (hu : Admissible w A m d u) {x : α} (hx : x ∉ A) : w x ≤ u := by
  exact le_of_not_gt (fun h => hx (hu.2.2.1 x h))

end TalagrandThreshold.Selector

end OAI
