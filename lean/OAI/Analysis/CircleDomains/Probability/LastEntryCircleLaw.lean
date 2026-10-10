import OAI.Analysis.CircleDomains.Probability.LastEntryLaw
import OAI.Analysis.CircleDomains.Probability.CircleSupportedLaw

namespace OAI

/-! Exact probabilities of the collar arc events used in alternation. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def lastEntryCircleLaw (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (χ : X → UnitAddCircle) : ProbabilityMeasure UnitAddCircle :=
  (lastEntryLaw μ V).map χ

omit [SecondCountableTopology X] in
theorem lastEntryCircleLaw_apply (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V) (χ : X → UnitAddCircle) (hχ : Measurable χ)
    (l u : ℚ) :
    (lastEntryCircleLaw μ V χ : Measure UnitAddCircle) (rationalCircleArc l u) =
      (μ : Measure C(PathTime, X))
        {γ | χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc l u} := by
  rw [lastEntryCircleLaw, ProbabilityMeasure.map_apply' _ hχ.aemeasurable
    (measurableSet_rationalCircleArc l u)]
  rw [lastEntryLaw, ProbabilityMeasure.map_apply' _
    (measurable_lastEntryLocation V hV).aemeasurable
    (hχ (measurableSet_rationalCircleArc l u))]
  rfl

omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace C(PathTime, X)] in
theorem lastEntryCircleLaw_nullSingletonClass (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (c : UnitAddCircle → X) (hc : MeasurableEmbedding c)
    (hs : (lastEntryLaw μ V : Measure X) (range c)ᶜ = 0)
    [NullSingletonClass (lastEntryLaw μ V : Measure X)] :
    NullSingletonClass (lastEntryCircleLaw μ V hc.invFun : Measure UnitAddCircle) :=
  circle_supported_map_nullSingletonClass (lastEntryLaw μ V) c hc hs

end CircleDomainRigidity

end

end OAI
