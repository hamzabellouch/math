import OAI.Geometry.CylinderCovering.Convexity.SquaredCapDataDefinitions
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCapsDefinitions

namespace OAI

noncomputable section

namespace AngularCaps

open CylinderCovering

def squaredData (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) : AngularGeneral.Data :=
  withSquaredCaps τ η (AngularOrdinaryCaps.ordinaryData .radial N a τ η)

def SquaredCoverStatement : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 / 480 → ∀ M : ℝ, 0 ≤ M →
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧
      ∀ τ : ℝ, 0 < τ → τ < δ →
        ∀ (N : ℕ) (a : ℕ → ℝ), 0 < N → a 0 = -1 → a N = 1 →
          (∀ j < N, a j < a (j + 1)) →
          (∀ j < N, a (j + 1) - a j ≤ M * τ ^ 2) →
          AngularGeneral.Conclusion τ η A (squaredData N a τ η)

end AngularCaps

end

end OAI
