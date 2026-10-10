import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures
import OAI.Analysis.CircleDomains.Probability.CodePathLaws
import OAI.Analysis.CircleDomains.Probability.ProbabilityMixtureMap

namespace OAI

/-! The mean occupation, tuple measure, and untagged path law of a code mixture
are the corresponding mixtures of the original means and path laws. -/

open MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [MeasurableSpace Z]

theorem measurable_codePathLaw (d : PathCodeData X Y) :
    Measurable (codePathLaw d) :=
  measurable_probability_pushforward (codePath d) (measurable_codePath d)

theorem codePathLaw_probabilityMixture (d : PathCodeData X Y)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law) :
    codePathLaw d (probabilityMixture P law hlaw) =
      probabilityMixture P (fun z => codePathLaw d (law z))
        ((measurable_codePathLaw d).comp hlaw) :=
  probabilityMixture_map P law hlaw (codePath d) (measurable_codePath d)

theorem measurable_meanCodeTuple (d : PathCodeData X Y) :
    Measurable (meanCodeTuple d) :=
  (Measure.measurable_bind' (measurable_baseCodeTuple d)).comp measurable_subtype_coe

theorem meanCodeTuple_probabilityMixture (d : PathCodeData X Y)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law) :
    meanCodeTuple d (probabilityMixture P law hlaw) =
      (P : Measure Z).bind (fun z => meanCodeTuple d (law z)) := by
  exact Measure.bind_bind (measurable_subtype_coe.comp hlaw).aemeasurable
    (measurable_baseCodeTuple d).aemeasurable

variable [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_meanCodeOccupation (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) : Measurable (meanCodeOccupation d) :=
  (Measure.measurable_bind' (measurable_baseCodeOccupation d hU)).comp measurable_subtype_coe

theorem meanCodeOccupation_probabilityMixture (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law) :
    meanCodeOccupation d (probabilityMixture P law hlaw) =
      (P : Measure Z).bind (fun z => meanCodeOccupation d (law z)) := by
  exact Measure.bind_bind (measurable_subtype_coe.comp hlaw).aemeasurable
    (measurable_baseCodeOccupation d hU).aemeasurable

end CircleDomainRigidity

end

end OAI
