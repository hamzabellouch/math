import OAI.Probability.FreeIsing.Estimates.ProjectiveExtension

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.BrownianExistence

theorem exists_preWienerMeasure :
    ∃ ν : Measure (ℝ≥0 → ℝ), IsProbabilityMeasure ν ∧
      IsProjectiveLimit ν BrownianReal.projectiveFamily :=
  CountableProjective.exists_projective_limit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily

def preWienerMeasure : Measure (ℝ≥0 → ℝ) := Classical.choose exists_preWienerMeasure

instance : IsProbabilityMeasure preWienerMeasure :=
  (Classical.choose_spec exists_preWienerMeasure).1

theorem preWienerMeasure_projectiveLimit :
    IsProjectiveLimit preWienerMeasure BrownianReal.projectiveFamily :=
  (Classical.choose_spec exists_preWienerMeasure).2

theorem coordinate_isPreBrownianReal :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) => ω t) preWienerMeasure where
  hasLaw I := {
    aemeasurable := (Finset.measurable_restrict I).aemeasurable
    map_eq := preWienerMeasure_projectiveLimit I }

end Problem367.BrownianExistence

end

end OAI
