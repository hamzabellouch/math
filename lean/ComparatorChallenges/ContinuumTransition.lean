import Mathlib

namespace OAI

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

abbrev Space := EuclideanSpace ℝ (Fin 3)

noncomputable def radialPotential (φ : ℝ → ℝ) (x : Space) : EReal :=
  if x = 0 then ⊤ else (φ ‖x‖ : EReal)

noncomputable def energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) : EReal :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    radialPotential φ (x i - x j)

def Admissible (φ : ℝ → ℝ) : Prop :=
  Measurable (radialPotential φ) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    BddAbove (φ '' Icc a b) ∧ BddBelow (φ '' Icc a b)) ∧
  Tendsto φ (𝓝[>] (0 : ℝ)) atTop ∧
  (∃ r₁ r₂ a : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ 0 < a ∧
    ∀ r ∈ Icc r₁ r₂, φ r ≤ -a) ∧
  (∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r : ℝ => r ^ 2 * |φ r|) (Ioi R)) ∧
  (∃ B : ℝ, ∀ (N : ℕ) (x : Fin N → Space),
    ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)

def cube (L : ℝ) : Set Space :=
  {x | ∀ i, x i ∈ Icc (-L / 2) (L / 2)}

noncomputable def boltzmann (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    (x : Fin N → Space) : ℝ :=
  if energy φ x = ⊤ then 0 else Real.exp (-β * (energy φ x).toReal)

noncomputable def partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else
    (1 / (N.factorial : ℝ)) *
      ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x

def HasCanonicalFreeEnergy (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ β ρ : ℝ, 0 < β → 0 < ρ →
    Tendsto (fun L : ℝ => L⁻¹ ^ 3 * Real.log (partition φ β L ⌊ρ * L ^ 3⌋₊))
      atTop (𝓝 (-β * f β ρ))

def MainStatement : Prop :=
  ∃ (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (I : Set ℝ) (βc : ℝ),
    Admissible φ ∧
    Asymptotics.IsLittleO atTop φ (fun r : ℝ => r ^ (-3 : ℤ)) ∧
    HasCanonicalFreeEnergy φ f ∧
    IsOpen I ∧ OrdConnected I ∧ I.Nonempty ∧ I ⊆ Ioi 0 ∧
    βc ∈ Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) ∧
    ∀ ρ ∈ I, ∃ dminus dplus : ℝ,
      HasDerivWithinAt (fun β => f β ρ) dminus (Iic βc) βc ∧
      HasDerivWithinAt (fun β => f β ρ) dplus (Ici βc) βc ∧
      dplus < dminus

theorem main_theorem : MainStatement := by
  sorry

end ContinuumTemperature

end OAI
