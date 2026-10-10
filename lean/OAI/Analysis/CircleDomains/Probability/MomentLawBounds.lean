import OAI.Analysis.CircleDomains.Probability.PathLawMixtures

namespace OAI

/-! The countable nonnegative integral tests used for candidate path laws form
a Borel family and are preserved by arbitrary Borel probability mixtures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

theorem lintegral_probabilityMixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(probabilityMixture P law hlaw : Measure Ω) =
      ∫⁻ z, ∫⁻ x, f x ∂(law z : Measure Ω) ∂(P : Measure Z) := by
  exact Measure.lintegral_bind (measurable_subtype_coe.comp hlaw).aemeasurable hf.aemeasurable

def CountableMomentBounds (cost : ℕ → Ω → ℝ≥0∞) (budget : ℕ → ℝ≥0∞)
    (μ : ProbabilityMeasure Ω) : Prop :=
  ∀ n, ∫⁻ x, cost n x ∂(μ : Measure Ω) ≤ budget n

theorem measurableSet_countableMomentBounds (cost : ℕ → Ω → ℝ≥0∞)
    (hcost : ∀ n, Measurable (cost n)) (budget : ℕ → ℝ≥0∞) :
    MeasurableSet {μ : ProbabilityMeasure Ω | CountableMomentBounds cost budget μ} := by
  simp only [CountableMomentBounds, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_le ((Measure.measurable_lintegral (hcost n)).comp measurable_subtype_coe)
    measurable_const

theorem CountableMomentBounds.mixture (cost : ℕ → Ω → ℝ≥0∞)
    (hcost : ∀ n, Measurable (cost n)) (budget : ℕ → ℝ≥0∞)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    (hbound : ∀ᵐ z ∂(P : Measure Z), CountableMomentBounds cost budget (law z)) :
    CountableMomentBounds cost budget (probabilityMixture P law hlaw) := by
  intro n
  rw [lintegral_probabilityMixture P law hlaw (hcost n)]
  calc
    _ ≤ ∫⁻ _z, budget n ∂(P : Measure Z) :=
      lintegral_mono_ae (hbound.mono fun z hz => hz n)
    _ = budget n := by simp

end CircleDomainRigidity

end

end OAI
