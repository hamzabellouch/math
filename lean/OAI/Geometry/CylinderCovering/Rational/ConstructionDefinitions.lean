import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegralDefinitions
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegralDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace SlopeRational

def coefficientGap (d : ℝ) : ℝ := energyIntegral d - ceilingIntegral d

def AdmissiblePadding (q : ℝ → ℝ) : Prop :=
  (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < q ε) ∧
  Asymptotics.IsBigO (𝓝[>] (0 : ℝ)) q (fun ε => ε ^ 2) ∧
  Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (fun ε => ε ^ 3) q

def HasStrictFiniteCover (d ε q : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
    ∃ D : Fin m → RuledApproximation.Cylinder,
    (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
    lowerSweep d ε q ⊆ RuledApproximation.familySet C ∧
    upperSweep d ε q ⊆ RuledApproximation.familySet D ∧
    referenceTetrahedron ⊆ RuledApproximation.familySet C ∪ RuledApproximation.familySet D ∧
    RuledApproximation.familyArea C + RuledApproximation.familyArea D < physicalScale / 4 ∧
    CylinderCovering.relativeCost referenceTetrahedron C +
      CylinderCovering.relativeCost referenceTetrahedron D < 1 / 2

def AsymptoticStatement : Prop :=
  (∀ d : ℝ, 0 < d → ∀ q : ℝ → ℝ, AdmissiblePadding q →
    (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      referenceTetrahedron ⊆ lowerSweep d ε (q ε) ∪ upperSweep d ε (q ε)) ∧
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun ε => weightedCost d ε (q ε) / physicalScale -
        (1 / 8 + ε ^ 2 * (ceilingIntegral d - energyIntegral d) + q ε / 2))
      (fun ε => ε ^ 4)) ∧
  Tendsto ceilingIntegral (𝓝[>] (0 : ℝ)) (𝓝 (16 / 15360 : ℝ)) ∧
  Tendsto energyIntegral (𝓝[>] (0 : ℝ)) (𝓝 (17 / 15360 : ℝ))

def ApproximationEligibilityStatement : Prop :=
  ∀ d : ℝ, 0 < d → ∀ q : ℝ → ℝ, AdmissiblePadding q →
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      IsCompact (labelDomain d ε (q ε)) ∧
      volume (frontier (labelDomain d ε (q ε))) = 0 ∧
      RuledApproximation.SmoothNear ∞ (labelDomain d ε (q ε)) (field d) ∧
      (∀ p ∈ labelDomain d ε (q ε),
        RuledApproximation.HyperbolicAt (1 / 2) (fun z => ε • field d z) p) ∧
      (∀ p ∈ labelDomain d ε (q ε),
        RuledApproximation.HyperbolicAt (1 / 2) (fun z => -ε • field d z) p)

def PaddingSchedulesStatement : Prop :=
  (∃ d : ℝ, 0 < d ∧ 0 < coefficientGap d) ∧
  (∀ d : ℝ, 0 < d → 0 < coefficientGap d →
    (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      weightedCost d ε (ε ^ (5 / 2 : ℝ)) < physicalScale / 8 ∧
      HasStrictFiniteCover d ε (ε ^ (5 / 2 : ℝ))) ∧
    ∀ η : ℝ, 0 < η → η / 2 < coefficientGap d →
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        weightedCost d ε (η * ε ^ 2) < physicalScale / 8 ∧
        HasStrictFiniteCover d ε (η * ε ^ 2))

def ConstructionStatement : Prop :=
  CylinderCovering.minimumShadowArea referenceTetrahedron = physicalScale / 2 ∧
  AsymptoticStatement ∧ ApproximationEligibilityStatement ∧ PaddingSchedulesStatement

end SlopeRational

end

end OAI
