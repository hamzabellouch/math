import OAI.Geometry.CylinderCovering.Rational.DictionaryCostDefinitions
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegralDefinitions
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegralDefinitions

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RationalDictionary

def coefficientBaseDomain : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ |p 0| ≤ c0 * p 1}

def uncenteredEnergy (d0 : ℝ) : ℝ :=
  (1 / 2) * ∫ p in coefficientBaseDomain,
    v1 d0 (p 0) (p 1) ^ 2 + v2 d0 (p 0) (p 1) ^ 2

def uncenteredCeiling (d0 : ℝ) : ℝ :=
  ∫ u in (-c0)..c0, a0 d0 u

def coefficientGap (d0 : ℝ) : ℝ :=
  uncenteredEnergy d0 - uncenteredCeiling d0

def CoefficientLimitsStatement : Prop :=
  Tendsto uncenteredEnergy (𝓝[>] (0 : ℝ))
    (𝓝 (c0 ^ 3 / 6 + 7 * c0 ^ 5 / 30)) ∧
  Tendsto uncenteredCeiling (𝓝[>] (0 : ℝ)) (𝓝 (8 * c0 ^ 5 / 15)) ∧
  Tendsto coefficientGap (𝓝[>] (0 : ℝ)) (𝓝 (c0 ^ 3 / 60)) ∧
  ∃ d0 : ℝ, 0 < d0 ∧ 0 < coefficientGap d0

end RationalDictionary

end

end OAI
