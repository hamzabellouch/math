import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators NNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Potential := ℝ≥0 → ℝ

def cube (L : ℝ) : Set Position :=
  {x | ∀ k : Fin 3, 0 ≤ x k ∧ x k ≤ L}

def configurationCube (L : ℝ) (N : ℕ) : Set (Fin N → Position) :=
  {x | ∀ i : Fin N, x i ∈ cube L}

def energy (φ : Potential) {N : ℕ} (x : Fin N → Position) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N with i < j, φ (nndist (x i) (x j))

def partition (φ : Potential) (L : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  (N.factorial : ℝ)⁻¹ *
    ∫ x in configurationCube L N, Real.exp (-β * energy φ x)

def packingNumber (L : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ X : Finset Position, X.card = n ∧
    (∀ x ∈ X, x ∈ cube L) ∧
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)}

def IsPackingDensity (p : ℝ) : Prop :=
  Tendsto (fun L : ℝ => (packingNumber L : ℝ) / L ^ 3) atTop (nhds p)

def IsBoundedPotential (φ : Potential) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ≥0, |φ r| ≤ M

def StableWith (φ : Potential) (B : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Position), -(B * N) ≤ energy φ x

def AlgebraicDecayWith (φ : Potential) (C : ℝ) : Prop :=
  ∀ r : ℝ≥0, 1 ≤ r → |φ r| ≤ C * (r : ℝ) ^ (-(3 : ℝ) - 1 / 32)

def IsCanonicalFreeEnergy (φ : Potential) (ρ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 < β →
    Tendsto (fun L : ℝ =>
      -(Real.log (partition φ L ⌊ρ * L ^ 3⌋₊ β) / (β * L ^ 3)))
      atTop (nhds (f β))

def StrictTemperatureCorner (f : ℝ → ℝ) (βc : ℝ) : Prop :=
  ∃ dLeft dRight : ℝ,
    HasDerivWithinAt f dLeft (Iic βc) βc ∧
    HasDerivWithinAt f dRight (Ici βc) βc ∧
    dRight < dLeft ∧ ¬DifferentiableAt ℝ f βc

theorem main :
    ∃ (p : ℝ) (φ : Potential) (B C : ℝ) (f : ℝ → ℝ) (βc : ℝ),
      0 < p ∧ IsPackingDensity p ∧
      IsBoundedPotential φ ∧ Continuous φ ∧
      0 < B ∧ 0 < C ∧ StableWith φ B ∧ AlgebraicDecayWith φ C ∧
      IsCanonicalFreeEnergy φ (5*p/3) f ∧
      βc ∈ Icc (7/8:ℝ) (9/8) ∧ StrictTemperatureCorner f βc := by
  sorry

end RadialTransition

end

end OAI
