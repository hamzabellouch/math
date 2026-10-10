import OAI.Probability.StrongRayleigh.CantorProjective

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.BrownianConstruction

theorem exists_preBrownianMeasure :
    ∃ μ : ProbabilityMeasure (ℝ≥0 → ℝ),
      IsPreBrownianReal (fun t ω => ω t) (μ : Measure (ℝ≥0 → ℝ)) := by
  obtain ⟨μ, hμ⟩ := CantorProjective.real_projective_exists
    BrownianReal.projectiveFamily BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  refine ⟨μ, ⟨fun I => ?_⟩⟩
  exact ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩

def preBrownianMeasure : ProbabilityMeasure (ℝ≥0 → ℝ) :=
  Classical.choose exists_preBrownianMeasure

theorem isPreBrownianReal_preBrownianMeasure :
    IsPreBrownianReal (fun t ω => ω t)
      (preBrownianMeasure : Measure (ℝ≥0 → ℝ)) :=
  Classical.choose_spec exists_preBrownianMeasure

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
