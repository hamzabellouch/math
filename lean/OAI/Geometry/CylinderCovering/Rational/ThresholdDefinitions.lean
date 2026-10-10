import OAI.Geometry.CylinderCovering.Rational.InversionDefinitions

namespace OAI

noncomputable section
namespace SlopeRational

def threshold (d ε x y : ℝ) : ℝ :=
  ε * alpha d * x * y +
    ε ^ 2 * (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y)

def ThresholdInclusionStatement : Prop :=
  ∀ d : ℝ, 0 < d → ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
    ∀ ε q x y t : ℝ, 0 < ε → ε < δ → C * ε ^ 3 ≤ q →
      |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → |t| ≤ 1 / 2 →
      vec2 y t ∈ wedge → threshold d ε x y ≤ t →
      ∃ p ∈ labelDomain d ε q, tiltedMap d (ε * x) p = vec2 y t

end SlopeRational

end

end OAI
