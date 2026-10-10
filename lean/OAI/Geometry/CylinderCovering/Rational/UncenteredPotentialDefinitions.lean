import OAI.Geometry.CylinderCovering.Rational.DictionaryDefinitions

namespace OAI

noncomputable section

namespace RationalDictionary

def streamPotential (d0 u s : ℝ) : ℝ :=
  g d0 s * (u ^ 2 - c0 ^ 2 * s ^ 2) / 2

def gSecond (d0 s : ℝ) : ℝ := 2 * (1 + d0) / (s + d0) ^ 3

def UncenteredStreamStatement : Prop :=
  ∀ d0 u s : ℝ, s + d0 ≠ 0 →
    HasDerivAt (fun y => streamPotential d0 y s) (v2 d0 u s) u ∧
    HasDerivAt (fun t => streamPotential d0 u t) (-v1 d0 u s) s ∧
    HasDerivAt (gPrime d0) (gSecond d0 s) s ∧
    g d0 s * gSecond d0 s / 2 = gPrime d0 s ^ 2 ∧
    v1 d0 (c0 * s) s = c0 * v2 d0 (c0 * s) s ∧
    v1 d0 (-c0 * s) s = -c0 * v2 d0 (-c0 * s) s

end RationalDictionary

end

end OAI
