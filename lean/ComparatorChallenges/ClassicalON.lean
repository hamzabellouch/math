import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

abbrev Site := ℤ × ℤ

def PositiveNeighbor (x y : Site) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 ∧ y.2 = x.2 + 1)

structure LatticeGraph where
  vertices : Finset Site
  edges : Finset (vertices × vertices)
  nearest : ∀ e ∈ edges, PositiveNeighbor e.1.val e.2.val

abbrev Spin (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
abbrev Configuration (n : ℕ) (G : LatticeGraph) := G.vertices → Spin n

def sphereProbability (n : ℕ) : Measure (Spin n) :=
  let surface := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  (surface Set.univ)⁻¹ • surface

def referenceLaw (n : ℕ) (G : LatticeGraph) : Measure (Configuration n G) :=
  Measure.pi (fun _ => sphereProbability n)

def interaction (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ)
    (σ : Configuration n G) : ℝ :=
  ∑ e : G.edges, b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ

def partition (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ) : ℝ :=
  ∫ σ, Real.exp (interaction n G b σ) ∂referenceLaw n G

def correlation (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ)
    (x y : G.vertices) : ℝ :=
  (∫ σ, ⟪(σ x).val, (σ y).val⟫_ℝ * Real.exp (interaction n G b σ)
    ∂referenceLaw n G) / partition n G b

def siteDistance (x y : Site) : ℝ :=
  Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 + ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2)

def ExponentialDecay : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (β : ℝ), 0 < β →
    ∃ A m : ℝ, 0 < m ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ x y : G.vertices,
        0 ≤ correlation n G b x y ∧
          correlation n G b x y ≤ A * Real.exp (-m * siteDistance x.val y.val)

theorem main : ExponentialDecay := by
  sorry

end ClassicalON

end

end OAI
