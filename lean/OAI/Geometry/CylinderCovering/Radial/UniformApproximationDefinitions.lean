import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.RadialUniformApproximation
open RadialSweep

def triangleCost (D : Data) (N : ℕ) (tag : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, TriangularCovering.area (frozenBase D N tag i)

def leadingCost (D : Data) (N : ℕ) (tag : Fin N → ℝ) : ℝ :=
  kappa D / 2 * RadialRiemann.collarSum D.R
    (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2)) 0 D.α D.β N tag

def collarError (D : Data) (N : ℕ) (tag : Fin N → ℝ) : ℝ :=
  triangleCost D N tag - leadingCost D N tag

structure Statement : Prop where
  collarUniform : ∀ D : Data, ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 0 < N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      0 ≤ collarError D N tag ∧ collarError D N tag ≤ C / N
  collarExplicit : ∀ D : Data, ∀ M : ℝ,
    (∀ t ∈ Icc D.α D.β, D.R t ≤ M) →
    ∀ N : ℕ, 0 < N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      0 ≤ collarError D N tag ∧
      collarError D N tag ≤ kappa D / 2 * (D.β - D.α) *
        (2 * M * (radialError D + collar D) * RadialRiemann.step D.α D.β N +
          (radialError D + collar D)^2 * (RadialRiemann.step D.α D.β N)^2) ∧
      collarError D N tag ≤ (kappa D / 2 * (D.β - D.α)^2 *
        (2 * M * (radialError D + collar D) +
          (radialError D + collar D)^2 * (D.β - D.α))) / N
  tagsUniform : ∀ D : Data, ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      |triangleCost D N tag - weightedArea D| < ε ∧
        actualCost D N tag ≤ weightedArea D + ε

end CylinderCovering.RadialUniformApproximation

end

end OAI
