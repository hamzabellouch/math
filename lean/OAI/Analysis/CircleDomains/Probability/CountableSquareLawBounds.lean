import OAI.Analysis.CircleDomains.Probability.ProbabilitySquareBounds
import OAI.Analysis.CircleDomains.Probability.MomentLawBounds

namespace OAI

/-! Countably prescribed visit bounds define a Borel family of laws and are
preserved under probability mixtures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

def CountableSquareLawBounds (v : S → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (μ : ProbabilityMeasure Ω) : Prop :=
  ∀ F : Finset S, ∑ s ∈ F, (∫⁻ w, v s w ∂(μ : Measure Ω)) ^ 2 ≤ budget

theorem measurableSet_countableSquareLawBounds [Countable S]
    (v : S → Ω → ℝ≥0∞) (hv : ∀ s, Measurable (v s)) (budget : ℝ≥0∞) :
    MeasurableSet {μ : ProbabilityMeasure Ω | CountableSquareLawBounds v budget μ} := by
  simp only [CountableSquareLawBounds, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro F
  apply measurableSet_le _ measurable_const
  exact Finset.measurable_sum F fun s _ =>
    (((Measure.measurable_lintegral (hv s)).comp measurable_subtype_coe).pow_const 2)

theorem CountableSquareLawBounds.mixture
    (v : S → Ω → ℝ≥0∞) (hv : ∀ s, Measurable (v s)) (budget : ℝ≥0∞)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    (hbound : ∀ᵐ z ∂(P : Measure Z), CountableSquareLawBounds v budget (law z)) :
    CountableSquareLawBounds v budget (probabilityMixture P law hlaw) := by
  intro F
  simp_rw [lintegral_probabilityMixture P law hlaw (hv _)]
  apply finite_square_moment_mixture_bound (P : Measure Z) F
    (fun s z => ∫⁻ w, v s w ∂(law z : Measure Ω))
    (fun s _ => (Measure.measurable_lintegral (hv s)).comp
      (measurable_subtype_coe.comp hlaw)) budget
  exact hbound.mono fun z hz => hz F

end CircleDomainRigidity

end

end OAI
