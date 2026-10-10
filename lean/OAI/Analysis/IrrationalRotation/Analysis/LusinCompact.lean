import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

open Set MeasureTheory
open scoped Topology ENNReal

namespace Invariant233.CompactTransfer

theorem continuousOn_of_finer_compact {X Y : Type*}
    {t t' : TopologicalSpace X} [TopologicalSpace Y] [@T2Space X t]
    (hle : t' ≤ t) {K : Set X} (hK : @IsCompact X t' K)
    {f : X → Y} (hf : @Continuous X Y t' _ f) :
    @ContinuousOn X Y t _ f K := by
  let s : TopologicalSpace K := @TopologicalSpace.induced K X Subtype.val t
  let s' : TopologicalSpace K := @TopologicalSpace.induced K X Subtype.val t'
  have hcomp : @CompactSpace K s' := (@isCompact_iff_compactSpace X t' K).mp hK
  have hT2 : @T2Space K s := inferInstance
  have hid : @Continuous K K s' s id := continuous_id_of_le (induced_mono hle)
  let e : @Homeomorph K K s' s :=
    @Continuous.homeoOfEquivCompactToT2 K K s' s hcomp hT2 (Equiv.refl K) hid
  apply (@continuousOn_iff_continuous_domRestrict X Y t _ f K).mpr
  have hff : @Continuous K Y s' _ (K.domRestrict f) :=
    @Continuous.comp K X Y s' t' _ Subtype.val f hf (@continuous_subtype_val X t' K)
  exact @Continuous.comp K K Y s s' _ _ _ hff
    (@Homeomorph.continuous K K s s' (@Homeomorph.symm K K s' s e))

theorem exists_isCompact_continuousOn {X Y : Type*}
    [t : TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨t', hle, hcont, hpolish⟩ := hf.exists_continuous
  have hborel : @BorelSpace X t' _ := by
    constructor
    exact (@BorelSpace.measurable_eq X t _ inferInstance).trans
      (@borel_eq_borel_of_le X t' t hpolish (inferInstance : @PolishSpace X t) hle).symm
  have hregular : @Measure.InnerRegularCompactLTTop X _ t' μ := by
    let := t'
    let := hpolish
    let := hborel
    infer_instance
  obtain ⟨K, _, hK, hμK⟩ := @MeasurableSet.exists_isCompact_sdiff_lt X _ μ t'
    (by let := t'; let := hborel; infer_instance)
    (by let := t'; let := hpolish; infer_instance)
    hregular Set.univ MeasurableSet.univ (measure_ne_top μ Set.univ) ε hε
  refine ⟨K, ?_, ?_, continuousOn_of_finer_compact hle hK hcont⟩
  · simpa only [Set.image_id] using
      (@IsCompact.image X X t' t K id hK (continuous_id_of_le hle))
  · simpa only [Set.compl_eq_univ_sdiff] using hμK

theorem exists_isCompact_forall_continuousOn {X ι : Type*} {Y : ι → Type*}
    [Countable ι] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [∀ i, TopologicalSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]
    [∀ i, MeasurableSpace (Y i)] [∀ i, OpensMeasurableSpace (Y i)]
    (μ : Measure X) [IsFiniteMeasure μ] {f : ∀ i, X → Y i}
    (hf : ∀ i, Measurable (f i)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ∀ i, ContinuousOn (f i) K := by
  obtain ⟨K, hK, hμK, hcont⟩ := exists_isCompact_continuousOn μ
    (Measurable.of_eval hf) hε
  exact ⟨K, hK, hμK, fun i => (continuous_apply i).comp_continuousOn hcont⟩

end Invariant233.CompactTransfer

end OAI
