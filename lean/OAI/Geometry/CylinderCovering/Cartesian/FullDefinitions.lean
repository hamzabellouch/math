import OAI.Geometry.CylinderCovering.Cartesian.StatementDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.CoverDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering

def CartesianCaps.untruncated (τ η q : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ s ≤ CartesianCaps.height τ η (q*s)}

def CartesianCutoffStatement : Prop :=
  ∀ τ η q : ℝ, τ ∈ Set.Ioc (0 : ℝ) (1/4) →
    η ∈ Set.Ioc (0 : ℝ) 1 → q ≠ 0 → |q| ≤ 1 →
    ¬ BddAbove (CartesianCaps.untruncated τ η q) ∧
    ¬ IsPreconnected (CartesianCaps.untruncated τ η q) ∧
    ∃ B : ℝ, 1 ≤ B ∧ Set.Ici B ⊆ CartesianCaps.untruncated τ η q

def CartesianFullStatement : Prop :=
  CartesianApertureStatement ∧ CartesianCoverStatement ∧ CartesianCutoffStatement

end CylinderCovering

end

end OAI
