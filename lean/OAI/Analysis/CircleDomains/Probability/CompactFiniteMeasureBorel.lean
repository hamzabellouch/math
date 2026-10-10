import OAI.Analysis.CircleDomains.Probability.CompactFiniteMeasureMeasurability
import OAI.Analysis.CircleDomains.Probability.CompactProbabilityBorel
import OAI.Analysis.CircleDomains.Selection.CompleteEmbeddingGDelta

namespace OAI

/-! Compact families of finite measures retain their original evaluation
sigma algebra. A countable continuous and measurable code proves both
compact-set measurability and the Borel structure on each compact family. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma exists_finiteMeasure_countable_code
    (Z : Type*) [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] :
    ∃ e : FiniteMeasure Z → (ℕ → ℝ≥0), Continuous e ∧ Measurable e ∧ Injective e := by
  let : MetricSpace Z := metrizableSpaceMetric Z
  obtain ⟨f,hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := Z)
  have hfm : MeasurableEmbedding f := hf.continuous.measurableEmbedding hf.injective
  let X := ℕ → unitInterval
  let : SeparableSpace (X →ᵇ ℝ≥0) :=
    (ContinuousMap.isometryEquivBoundedOfCompact X ℝ≥0).surjective.denseRange.separableSpace
      (ContinuousMap.isometryEquivBoundedOfCompact X ℝ≥0).continuous
  obtain ⟨b,hb⟩ := exists_dense_seq (X →ᵇ ℝ≥0)
  let e : FiniteMeasure Z → (ℕ → ℝ≥0) :=
    fun v n => (v.map f).testAgainstNN (b n)
  have hec : Continuous e := continuous_pi (fun n =>
    (FiniteMeasure.continuous_testAgainstNN_eval (b n)).comp
      (FiniteMeasure.continuous_map hf.continuous))
  have hem : Measurable e := by
    apply Measurable.of_eval
    intro n
    have hm : Measurable (fun v : FiniteMeasure Z =>
        (v.map f : Measure X)) :=
      (Measure.measurable_map f hfm.measurable).comp measurable_subtype_coe
    exact (Measure.measurable_lintegral
      ((ENNReal.continuous_coe.comp (b n).continuous).measurable)).ennreal_toNNReal.comp hm
  refine ⟨e,hec,hem,?_⟩
  intro v w heq
  have hm : v.map f = w.map f := by
    apply FiniteMeasure.injective_toWeakDualBCNN
    apply DFunLike.ext
    intro g
    exact hb.induction_on g
      (isClosed_eq (v.map f).testAgainstNN_lipschitz.continuous
        (w.map f).testAgainstNN_lipschitz.continuous)
      (fun n => congrFun heq n)
  apply FiniteMeasure.toMeasure_injective
  exact hfm.map_injective (congrArg FiniteMeasure.toMeasure hm)

lemma compact_finiteMeasure_measurableSet
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) : MeasurableSet S := by
  obtain ⟨e,hec,hem,hei⟩ := exists_finiteMeasure_countable_code Z
  have hclosed : IsClosed (e '' S) := (hS.image hec).isClosed
  convert hem hclosed.measurableSet using 1
  exact (preimage_image_eq S hei).symm

lemma compact_finiteMeasure_borel
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) : BorelSpace S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨e,hec,hem,hei⟩ := exists_finiteMeasure_countable_code Z
  have he : IsClosedEmbedding (fun v : S => e v.val) :=
    (hec.comp continuous_subtype_val).isClosedEmbedding (hei.comp Subtype.val_injective)
  have hm : Measurable (fun v : S => e v.val) := hem.comp measurable_subtype_coe
  refine ⟨le_antisymm (compact_finiteMeasure_measurable_le_borel S) ?_⟩
  rw [he.isEmbedding.eq_induced,borel_comap,← BorelSpace.measurable_eq]
  exact hm.comap_le

lemma compact_finiteMeasure_polish
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) : PolishSpace S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨e,hec,_,hei⟩ := exists_finiteMeasure_countable_code Z
  have he : IsClosedEmbedding (fun v : S => e v.val) :=
    (hec.comp continuous_subtype_val).isClosedEmbedding (hei.comp Subtype.val_injective)
  exact he.polishSpace

end CircleDomainRigidity

end

end OAI
