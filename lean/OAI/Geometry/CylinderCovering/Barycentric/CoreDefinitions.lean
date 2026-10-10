import OAI.Geometry.CylinderCovering.Barycentric.SweepsDefinitions

namespace OAI

namespace CylinderCovering

def BarycentricCoreStatement : Prop :=
  (∀ k : ℝ, IsCompact (RadialCoordinates.firstSweep k) ∧
    IsCompact (RadialCoordinates.secondSweep k)) ∧
  (∀ k : ℝ, 0 < k → k ≤ 1 / 5000 →
    RadialCoordinates.barycentricSimplex ⊆
      RadialCoordinates.firstSweep k ∪ RadialCoordinates.secondSweep k) ∧
  (∀ k : ℝ, |k| ≤ 1 / 2 →
    |RadialCoordinates.J k / Real.sqrt 2 - (1 / 8 - (11 / 3000) * k ^ 2)| ≤
      (47 / 16) * k ^ 4) ∧
  (∀ k : ℝ, 0 < k → k ≤ 1 / 5000 →
    2 * RadialCoordinates.J k < Real.sqrt 2 / 4) ∧
  (∀ a b z : ℝ, 0 < a → 0 < b →
    ∃! t : ℝ, t ∈ Set.Ioo 0 1 ∧ a / t - b / (1 - t) = z) ∧
  (∀ a b z : ℝ, 0 ≤ a → 0 ≤ b →
    ∃ t S : ℝ, t ∈ Set.Icc 0 1 ∧ 0 ≤ S ∧
      a = S * t + z * t ^ 2 ∧ b = S * (1 - t) - z * (1 - t) ^ 2)

end CylinderCovering

end OAI
