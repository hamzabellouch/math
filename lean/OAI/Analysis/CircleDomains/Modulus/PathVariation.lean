import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

namespace OAI

/-! Borel length data for ordinary continuous metric paths. These are applied
to physical-domain subarcs when forming the path occupation kernel. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathVariation_lowerSemicontinuous (A : Set PathTime) :
    LowerSemicontinuous (fun γ : C(PathTime, X) => eVariationOn γ A) := by
  unfold eVariationOn
  apply lowerSemicontinuous_iSup
  intro p
  apply Continuous.lowerSemicontinuous
  apply continuous_finsetSum
  intro i _
  exact (continuous_eval_const _).edist (continuous_eval_const _)

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathVariation (A : Set PathTime) :
    Measurable (fun γ : C(PathTime, X) => eVariationOn γ A) :=
  (pathVariation_lowerSemicontinuous A).measurable

theorem measurableSet_rectifiablePaths :
    MeasurableSet {γ : C(PathTime, X) | BoundedVariationOn γ univ} := by
  change MeasurableSet {γ : C(PathTime, X) | eVariationOn γ univ ≠ ∞}
  exact (measurable_pathVariation univ) (measurableSet_singleton ∞).compl

theorem measurable_pathVariationFromTo (a b : PathTime) :
    Measurable (fun γ : C(PathTime, X) => variationOnFromTo γ univ a b) := by
  classical
  unfold variationOnFromTo
  split
  · exact (measurable_pathVariation _).ennreal_toReal
  · exact (measurable_pathVariation _).ennreal_toReal.neg

end CircleDomainRigidity

end

end OAI
