import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

noncomputable def fiberValue (f : X → Y) (g : X → ℝ) (y : Y) : ℝ :=
  if h : ∃ x, f x = y then g h.choose else 0

lemma fiberValue_apply (f : X → Y) (g : X → ℝ)
    (hg : ∀ x x', f x = f x' → g x = g x') (x : X) : fiberValue f g (f x) = g x := by
  unfold fiberValue
  rw [dite_eq_left ⟨x,rfl⟩]
  exact hg _ x (Exists.choose_spec (show ∃ y, f y = f x from ⟨x,rfl⟩))

lemma fiberValue_nonneg (f : X → Y) (g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (y : Y) : 0 ≤ fiberValue f g y := by
  unfold fiberValue
  split_ifs
  · exact hg _
  · exact le_rfl

end CriticalPercolation.FiniteEntropy

end
end

end OAI
