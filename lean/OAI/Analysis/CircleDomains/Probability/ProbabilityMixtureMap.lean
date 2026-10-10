import OAI.Analysis.CircleDomains.Probability.PathLawMixtures

namespace OAI

/-! Measurable pushforwards commute with the actual Borel probability mixture. -/

open MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {Ω T Z : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace Z]

theorem measurable_probability_pushforward (f : Ω → T) (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure Ω => μ.map f) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map f hf).comp measurable_subtype_coe

theorem probabilityMixture_map
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    (f : Ω → T) (hf : Measurable f) :
    (probabilityMixture P law hlaw).map f =
      probabilityMixture P (fun z => (law z).map f)
        ((measurable_probability_pushforward f hf).comp hlaw) := by
  apply Subtype.ext
  ext E hE
  change ((P : Measure Z).bind (fun z => (law z : Measure Ω))).map f E =
    ((P : Measure Z).bind (fun z => ((law z).map f : Measure T))) E
  have hm : Measurable (fun z => (law z : Measure Ω)) :=
    measurable_subtype_coe.comp hlaw
  have hn : Measurable (fun z => ((law z).map f : Measure T)) :=
    measurable_subtype_coe.comp ((measurable_probability_pushforward f hf).comp hlaw)
  rw [Measure.map_apply hf hE, Measure.bind_apply (hf hE) hm.aemeasurable,
    Measure.bind_apply hE hn.aemeasurable]
  apply lintegral_congr
  intro z
  exact (Measure.map_apply hf hE).symm

end CircleDomainRigidity

end

end OAI
