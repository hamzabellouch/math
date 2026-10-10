import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# The published analytic input for result 200

Prékopa, *On logarithmic concave measures and functions*, Acta Sci. Math.
(Szeged) 34 (1973), 335–343, Theorem 3, equation (2.3), with two source
functions. Source: https://acta.bibl.u-szeged.hu/14411/1/math_034_335-343.pdf
The one-dimensional input is Leindler (1972), *On a certain converse of
Hölder's inequality II*, 217–223, as identified in Prékopa's §2.

The finite-box specialization allows positive continuous functions on a
common compact coordinate box and finite unions of open boxes.
-/

namespace ContingencyTables.PublishedInputs

open MeasureTheory

abbrev Point (q : ℕ) := Fin q → ℝ

/-- The bounded finite unions of open coordinate boxes used by the bin
conductance argument. Empty unions and empty coordinate boxes are allowed. -/
def IsFiniteBoxUnion {q : ℕ} (S : Set (Point q)) : Prop :=
  ∃ (n : ℕ) (lower upper : Fin n → Point q),
    S = {x | ∃ k : Fin n, ∀ i, lower k i < x i ∧ x i < upper k i}

/-- The weighted Minkowski interpolation with the manuscript convention. -/
def interpolate {q : ℕ} (t : ℝ) (S T : Set (Point q)) : Set (Point q) :=
  {z | ∃ x ∈ S, ∃ y ∈ T, z = (1 - t) • x + t • y}

/-- Precisely the previously published finite-box integral interpolation
input. The functions need only be positive and continuous on the common
compact coordinate box; all integrals are Lebesgue integrals. -/
def FiniteBoxPrekopaLeindler (q : ℕ) : Prop :=
  ∀ (t : ℝ), 0 < t → t < 1 →
  ∀ (lower upper : Point q) (S₀ S₁ S₂ : Set (Point q))
    (f₀ f₁ f₂ : Point q → ℝ),
    IsFiniteBoxUnion S₀ → IsFiniteBoxUnion S₁ → IsFiniteBoxUnion S₂ →
    closure S₀ ⊆ Set.Icc lower upper →
    closure S₁ ⊆ Set.Icc lower upper →
    closure S₂ ⊆ Set.Icc lower upper →
    ContinuousOn f₀ (Set.Icc lower upper) →
    ContinuousOn f₁ (Set.Icc lower upper) →
    ContinuousOn f₂ (Set.Icc lower upper) →
    (∀ x ∈ Set.Icc lower upper, 0 < f₀ x) →
    (∀ x ∈ Set.Icc lower upper, 0 < f₁ x) →
    (∀ x ∈ Set.Icc lower upper, 0 < f₂ x) →
    interpolate t S₁ S₂ ⊆ S₀ →
    (∀ x ∈ S₁, ∀ y ∈ S₂,
      (f₁ x) ^ (1 - t) * (f₂ y) ^ t ≤ f₀ ((1 - t) • x + t • y)) →
    (∫ x in S₁, f₁ x) ^ (1 - t) * (∫ y in S₂, f₂ y) ^ t ≤
      ∫ z in S₀, f₀ z

/-- Log-concavity is needed only on the common ambient box. -/
def LogConcaveOn {q : ℕ} (ρ : Point q → ℝ) (K : Set (Point q)) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 < t → t < 1 →
    (ρ x) ^ (1 - t) * (ρ y) ^ t ≤ ρ ((1 - t) • x + t • y)

/-- Specialization of the published input to the one log-concave density
used for bin conductance. The geometric hypotheses specify the common ambient box. -/
theorem density_interpolation {q : ℕ} (hPL : FiniteBoxPrekopaLeindler q)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (lower upper : Point q) (S T : Set (Point q)) (ρ : Point q → ℝ)
    (hS : IsFiniteBoxUnion S) (hT : IsFiniteBoxUnion T)
    (hM : IsFiniteBoxUnion (interpolate t S T))
    (hSc : closure S ⊆ Set.Icc lower upper)
    (hTc : closure T ⊆ Set.Icc lower upper)
    (hMc : closure (interpolate t S T) ⊆ Set.Icc lower upper)
    (hρ : ContinuousOn ρ (Set.Icc lower upper))
    (hpos : ∀ x ∈ Set.Icc lower upper, 0 < ρ x)
    (hlc : LogConcaveOn ρ (Set.Icc lower upper)) :
    (∫ x in S, ρ x) ^ (1 - t) * (∫ y in T, ρ y) ^ t ≤
      ∫ z in interpolate t S T, ρ z := by
  apply hPL t ht ht1 lower upper (interpolate t S T) S T ρ ρ ρ
    hM hS hT hMc hSc hTc hρ hρ hρ hpos hpos hpos Set.Subset.rfl
  intro x hx y hy
  exact hlc x (hSc (subset_closure hx)) y (hTc (subset_closure hy)) t ht ht1

end ContingencyTables.PublishedInputs

end OAI
