import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-!
# Finite families, containment covers, and exceptional sets

All families are ordinary finite sets: repeated generators carry no extra cost.
In contrast, the members of a union tuple may repeat. The exceptional family
uses containment in a union, without any monotonicity assumption on the input.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

abbrev Family (α : Type*) := Finset (Finset α)

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/-- The mass of a subset under independent Bernoulli coordinates. -/
def bernoulliMass (p : ℝ) (s : Finset α) : ℝ :=
  p ^ s.card * (1 - p) ^ (Finset.univ \ s).card

/-- The Bernoulli measure of an arbitrary finite family. -/
def familyMeasure (p : ℝ) (D : Family α) : ℝ :=
  ∑ s ∈ D, bernoulliMass p s

/-- Cost at the specified density, counting each generator once. -/
def cost (p : ℝ) (G : Family α) : ℝ := ∑ I ∈ G, p ^ I.card

/-- A cover supplies a contained generator for every target set. -/
def Covers (G A : Family α) : Prop := ∀ S ∈ A, ∃ I ∈ G, I ⊆ S

/-- Smallness is witnessed by an actual containment cover of cost at most one half. -/
def Small (p : ℝ) (A : Family α) : Prop :=
  ∃ G : Family α, Covers G A ∧ cost p G ≤ 1 / 2

/-- A union of exactly `k` entries; repetitions are allowed. -/
def unionTuple {k : ℕ} (f : Fin k → Finset α) : Finset α :=
  Finset.univ.biUnion f

/-- All unions of `k` members of a family. -/
def unionFamily (k : ℕ) (D : Family α) : Family α := by
  classical
  exact Finset.univ.filter (fun S =>
    ∃ f : Fin k → Finset α, (∀ j, f j ∈ D) ∧ unionTuple f = S)

/-- Sets contained in no union of `k` members of `D`. -/
def exceptional (k : ℕ) (D : Family α) : Family α := by
  classical
  exact Finset.univ.filter (fun S =>
    ∀ f : Fin k → Finset α, (∀ j, f j ∈ D) → ¬ S ⊆ unionTuple f)

/-- The subset represented by a Boolean coordinate vector. -/
def cubeSet (x : α → Bool) : Finset α :=
  Finset.univ.filter (fun i => x i = true)

/-- The indicator of a family on the Boolean cube. -/
def familyIndicator (D : Family α) (x : α → Bool) : ℝ :=
  if cubeSet x ∈ D then 1 else 0

end
end TalagrandDiscreteConvexity

end OAI
