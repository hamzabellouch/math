import Mathlib

namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

abbrev Cube (ι : Type*) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def character {ι : Type*} (s : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ s, sign (x i)

def fourierCoeff {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (s : Finset ι) : ℝ := by
  classical
  exact average (fun x => f x * character s x)

def fourierDegree {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Finset ι => fourierCoeff f s ≠ 0)).sup Finset.card

def IsBoolean {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = -1 ∨ f x = 1

def Nonconstant {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x y, f x ≠ f y

def singletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, fourierCoeff f {i}

def absoluteSingletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, |fourierCoeff f {i}|

def SignedViolations : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ Nonconstant f ∧ C * Real.sqrt (fourierDegree f) < singletonSum f

def AbsoluteRatios : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ 0 < fourierDegree f ∧
      r = absoluteSingletonSum f / Real.sqrt (fourierDegree f)}

/-- The two clauses of the literal main theorem. Unboundedness above is the
real-valued formulation of the displayed supremum being positive infinity. -/
theorem main : SignedViolations ∧ ¬ BddAbove AbsoluteRatios := by
  sorry

end SquareRootDegree

end

end OAI
