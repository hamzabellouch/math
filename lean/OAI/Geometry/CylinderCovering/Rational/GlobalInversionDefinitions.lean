import OAI.Geometry.CylinderCovering.Rational.InversionDefinitions

namespace OAI

namespace SlopeRational

def GlobalWedgeInversionStatement : Prop :=
  ∀ d : ℝ, 0 < d → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
    Set.BijOn (tiltedMap d s) wedge wedge

end SlopeRational

end OAI
