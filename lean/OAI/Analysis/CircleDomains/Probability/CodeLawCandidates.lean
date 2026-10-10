import OAI.Analysis.CircleDomains.Probability.CodeLawMixtures
import OAI.Analysis.CircleDomains.Probability.DensityBudgetMixture
import OAI.Analysis.CircleDomains.Probability.CountableSquareLawBounds
import OAI.Analysis.CircleDomains.Selection.VisitCounts

namespace OAI

/-! The quantitative family of code laws used in dust fusion is Borel and
closed under arbitrary Borel probability mixtures. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]


def codeVisitWeight (d : PathCodeData X Y) (a : S → X) (s : S) (Γ : BasePathCode d) : ℝ≥0∞ :=
  visitCount (codePath d Γ) (a s)

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_codeVisitWeight (d : PathCodeData X Y) (a : S → X) (s : S) :
    Measurable (codeVisitWeight d a s) :=
  measurable_visitCount.comp ((measurable_codePath d).prodMk measurable_const)

def CodeLawCandidate (d : PathCodeData X Y) (a : S → X) (μ : Measure Y)
    (τ : Measure LevelTuple) (massOcc massTuple energy visitBudget : ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) : Prop :=
  BoundedDensityBudget μ (meanCodeOccupation d P) massOcc energy ∧
    CountableSquareLawBounds (codeVisitWeight d a) visitBudget P ∧
    BoundedDensityBudget τ (meanCodeTuple d P) massTuple energy

theorem measurableSet_codeLawCandidate [Countable S]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (a : S → X)
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (massOcc massTuple energy visitBudget : ℝ≥0∞)
    (hOcc : massOcc < ∞) (hTuple : massTuple < ∞) :
    MeasurableSet {P | CodeLawCandidate d a μ τ massOcc massTuple energy visitBudget P} := by
  exact (measurableSet_boundedDensityBudget (meanCodeOccupation d)
    (measurable_meanCodeOccupation d hU) μ massOcc energy hOcc).inter
    ((measurableSet_countableSquareLawBounds (codeVisitWeight d a)
      (measurable_codeVisitWeight d a) visitBudget).inter
    (measurableSet_boundedDensityBudget (meanCodeTuple d) (measurable_meanCodeTuple d)
      τ massTuple energy hTuple))

theorem CodeLawCandidate.mixture [MeasurableSpace Z]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (a : S → X)
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (massOcc massTuple energy visitBudget : ℝ≥0∞)
    (hOcc : massOcc < ∞) (hTuple : massTuple < ∞)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law)
    (h : ∀ z, CodeLawCandidate d a μ τ massOcc massTuple energy visitBudget (law z)) :
    CodeLawCandidate d a μ τ massOcc massTuple energy visitBudget
      (probabilityMixture P law hlaw) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [meanCodeOccupation_probabilityMixture d hU P law hlaw]
    exact boundedDensityBudget_bind (fun z => meanCodeOccupation d (law z))
      ((measurable_meanCodeOccupation d hU).comp hlaw) μ massOcc energy hOcc
      (fun z => (h z).1) (P : Measure Z)
  · exact CountableSquareLawBounds.mixture (codeVisitWeight d a)
      (measurable_codeVisitWeight d a) visitBudget P law hlaw
      (Eventually.of_forall fun z => (h z).2.1)
  · rw [meanCodeTuple_probabilityMixture d P law hlaw]
    exact boundedDensityBudget_bind (fun z => meanCodeTuple d (law z))
      ((measurable_meanCodeTuple d).comp hlaw) τ massTuple energy hTuple
      (fun z => (h z).2.2) (P : Measure Z)

end CircleDomainRigidity

end

end OAI
