import OAI.Analysis.CircleDomains.Sobolev.WeakProbabilityMeasurability
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

namespace OAI

/-! On a compact metrizable space, countably many continuous test integrals
embed the probability laws in a countable product. Their weak topology is
Polish and its Borel sigma algebra is precisely the evaluation sigma algebra. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma compact_probability_borel
    (Z : Type*) [TopologicalSpace Z] [MetrizableSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] : BorelSpace (ProbabilityMeasure Z) := by
  let : MetricSpace Z := TopologicalSpace.metrizableSpaceMetric Z
  let : SeparableSpace (Z →ᵇ ℝ≥0) :=
    (ContinuousMap.isometryEquivBoundedOfCompact Z ℝ≥0).surjective.denseRange.separableSpace
      (ContinuousMap.isometryEquivBoundedOfCompact Z ℝ≥0).continuous
  obtain ⟨b, hb⟩ := exists_dense_seq (Z →ᵇ ℝ≥0)
  let e : ProbabilityMeasure Z → (ℕ → ℝ≥0) :=
    fun μ n => μ.toFiniteMeasure.testAgainstNN (b n)
  have hec : Continuous e := continuous_pi (fun n =>
    ProbabilityMeasure.continuous_testAgainstNN_eval (b n))
  have hei : Injective e := by
    intro μ ν heq
    apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding Z).injective
    apply FiniteMeasure.injective_toWeakDualBCNN
    apply DFunLike.ext
    intro f
    change μ.toFiniteMeasure.testAgainstNN f = ν.toFiniteMeasure.testAgainstNN f
    exact hb.induction_on f
      (isClosed_eq μ.toFiniteMeasure.testAgainstNN_lipschitz.continuous
        ν.toFiniteMeasure.testAgainstNN_lipschitz.continuous)
      (fun n => congrFun heq n)
  have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
  have hem : Measurable e := by
    apply Measurable.of_eval
    intro n
    exact (Measure.measurable_lintegral ((ENNReal.continuous_coe.comp (b n).continuous).measurable)).ennreal_toNNReal.comp
      measurable_subtype_coe
  have hlo : (inferInstance : MeasurableSpace (ProbabilityMeasure Z)) ≤ borel (ProbabilityMeasure Z) := by
    have h : @Measurable (ProbabilityMeasure Z) (Measure Z)
        (borel (ProbabilityMeasure Z)) inferInstance (fun μ => (μ : Measure Z)) := by
      let : MeasurableSpace (ProbabilityMeasure Z) := borel (ProbabilityMeasure Z)
      let : BorelSpace (ProbabilityMeasure Z) := ⟨rfl⟩
      exact measurable_measure_of_continuous_probability continuous_id
    exact h.comap_le
  have hup : borel (ProbabilityMeasure Z) ≤ (inferInstance : MeasurableSpace (ProbabilityMeasure Z)) := by
    rw [he.isEmbedding.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
    exact hem.comap_le
  exact ⟨le_antisymm hlo hup⟩

lemma compact_probability_polish
    (Z : Type*) [TopologicalSpace Z] [MetrizableSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] : PolishSpace (ProbabilityMeasure Z) := by
  let : MetricSpace (ProbabilityMeasure Z) := TopologicalSpace.metrizableSpaceMetric _
  infer_instance

end CircleDomainRigidity

end

end OAI
