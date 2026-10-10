import OAI.Analysis.CircleDomains.Modulus.HitNormTopology

namespace OAI

/-! Path hits tested on a compact subset of the ambient path space.  The
continuous map is the inclusion of the dust in the application; no path is
required to lie in that subset. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)]
  (ι : C(X, Y))

def pathHitProbability (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) : ℝ≥0∞ :=
  CircleDomainRigidity.pathHitProbability μ (ι x)

def pathHitReal (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) : ℝ :=
  (pathHitProbability ι μ x).toReal

theorem pathHitProbability_le_one (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) :
    pathHitProbability ι μ x ≤ 1 :=
  CircleDomainRigidity.pathHitProbability_le_one μ (ι x)

theorem pathHitReal_nonneg (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) :
    0 ≤ pathHitReal ι μ x := ENNReal.toReal_nonneg

theorem pathHitReal_le_one (μ : ProbabilityMeasure C(PathTime, Y)) (x : X) :
    pathHitReal ι μ x ≤ 1 :=
  CircleDomainRigidity.pathHitReal_le_one μ (ι x)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)]

theorem measurable_pathHitProbability_point (μ : ProbabilityMeasure C(PathTime, Y)) :
    Measurable (pathHitProbability ι μ) :=
  (CircleDomainRigidity.measurable_pathHitProbability_point μ).comp ι.continuous.measurable

omit [MeasurableSpace X] [BorelSpace X] in
theorem pathHitReal_upperSemicontinuous :
    UpperSemicontinuous (fun p : ProbabilityMeasure C(PathTime, Y) × X =>
      pathHitReal ι p.1 p.2) :=
  CircleDomainRigidity.pathHitReal_upperSemicontinuous.comp
    (continuous_fst.prodMk (ι.continuous.comp continuous_snd))

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] in
theorem integrable_pathHitReal {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) {law : Z → ProbabilityMeasure C(PathTime, Y)}
    (hlaw : Measurable law) (x : X) :
    Integrable (fun z => pathHitReal ι (law z) x) (P : Measure Z) :=
  CircleDomainRigidity.integrable_pathHitReal P hlaw (ι x)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] in
theorem pathHitReal_mixture {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure C(PathTime, Y))
    (hlaw : Measurable law) (x : X) :
    pathHitReal ι (probabilityMixture P law hlaw) x =
      ∫ z, pathHitReal ι (law z) x ∂(P : Measure Z) :=
  CircleDomainRigidity.pathHitReal_mixture P law hlaw (ι x)

end CircleDomainRigidity.MarkedHit

end

end OAI
