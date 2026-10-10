import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions

namespace OAI

noncomputable section
namespace SlopeRational

def ceilingIntegral (d : ℝ) : ℝ :=
  ∫ Y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), ceilingPolynomial d Y

end SlopeRational

end

end OAI
