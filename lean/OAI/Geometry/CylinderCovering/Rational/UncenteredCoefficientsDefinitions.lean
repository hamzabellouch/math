import OAI.Geometry.CylinderCovering.Rational.DictionaryDefinitions
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegralDefinitions
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegralDefinitions

namespace OAI

noncomputable section
open MeasureTheory
namespace RationalDictionary

def uncenteredBaseDomain : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ |p 0| ≤ c0 * p 1}

def uncenteredEnergyIntegral (d0 : ℝ) : ℝ :=
  (1 / 2) * ∫ p in uncenteredBaseDomain, ‖velocity d0 p‖ ^ 2

def uncenteredCeilingIntegral (d0 : ℝ) : ℝ :=
  ∫ u in -c0..c0, a0 d0 u

def uncenteredCoefficientGap (d0 : ℝ) : ℝ :=
  uncenteredEnergyIntegral d0 - uncenteredCeilingIntegral d0

def coefficientScale (d0 : ℝ) : ℝ := 32 * (1 + d0) ^ 2 / ell

end RationalDictionary

end

end OAI
