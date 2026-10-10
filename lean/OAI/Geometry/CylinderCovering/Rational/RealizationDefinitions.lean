import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace SlopeRational

abbrev Space := EuclideanSpace ℝ (Fin 3)

def physicalScale : ℝ := 1 / Real.sqrt 2

def referenceTetrahedron : Set Space :=
  {z | ∃ t : ℝ, -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 ∧
    |z 0| ≤ (1 / 2 + t) / 2 ∧ |z 1| ≤ (1 / 2 - t) / 2 ∧
    z 2 = physicalScale * t}

def reflection (z : Space) : Space :=
  RuledApproximation.vec3 (z 1) (z 0) (-z 2)

def lowerSweep (d ε q : ℝ) : Set Space :=
  RuledApproximation.physicalRuled physicalScale (labelDomain d ε q)
    (fun p => ε • field d p) (1 / 2)

def upperSweep (d ε q : ℝ) : Set Space :=
  reflection '' RuledApproximation.physicalRuled physicalScale (labelDomain d ε q)
    (fun p => -ε • field d p) (1 / 2)

def weightedCost (d ε q : ℝ) : ℝ :=
  physicalScale * ∫ p in labelDomain d ε q,
    RuledApproximation.physicalWeight physicalScale (ε • field d p)

def RationalCoverageStatement : Prop :=
  ∀ (d : ℝ) (q : ℝ → ℝ), 0 < d →
    (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < q ε) →
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ)) q (fun ε => ε ^ 2) →
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (fun ε => ε ^ 3) q →
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      referenceTetrahedron ⊆ lowerSweep d ε (q ε) ∪ upperSweep d ε (q ε)

end SlopeRational

end

end OAI
