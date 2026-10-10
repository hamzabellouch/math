import OAI.Geometry.CylinderCovering.Cartesian.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.CartesianCaps

def cartesianData (N : ℕ) (a : ℕ → ℝ) (τ η : ℝ) : AngularGeneral.Data :=
  withCartesianCaps τ η (AngularOrdinaryCaps.ordinaryData .radial N a τ η)

end CylinderCovering.CartesianCaps

namespace CylinderCovering

def CartesianCoverStatement : Prop :=
  ∀ η : ℝ, 0 < η → η < 1/480 → ∀ M : ℝ, 0 ≤ M →
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧
    ∀ τ : ℝ, 0 < τ → τ < δ → ∀ N : ℕ, ∀ a : ℕ → ℝ,
      0 < N → a 0 = -1 → a N = 1 →
      (∀ j < N, a j < a (j+1)) →
      (∀ j < N, a (j+1) - a j ≤ M*τ^2) →
      AngularGeneral.Conclusion τ η A (CartesianCaps.cartesianData N a τ η) ∧
      ∀ b ∈ Set.Icc (3/4 : ℝ) 1, ∀ j < N,
        AngularGeneral.lowerIntercept (CartesianCaps.cartesianData N a τ η) j =
          {z | ∃ q ∈ Set.Icc (a j) (a (j+1)),
            ∃ s ∈ CartesianCaps.aperture τ η b q,
              z = TriangularCovering.point 0 (q*s) s} ∧
        AngularGeneral.upperIntercept (CartesianCaps.cartesianData N a τ η) j =
          {z | ∃ q ∈ Set.Icc (a j) (a (j+1)),
            ∃ s ∈ CartesianCaps.aperture τ η b q,
              z = TriangularCovering.point (q*s) 0 (1-s)}

end CylinderCovering

end

end OAI
