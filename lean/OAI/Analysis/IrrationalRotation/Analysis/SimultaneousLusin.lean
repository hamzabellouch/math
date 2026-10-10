import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts

namespace OAI

open Set MeasureTheory Topology
open scoped ENNReal

namespace Invariant233.SimultaneousLusin

theorem continuousOn_of_finer_compact {X Y : Type*}
    [t : TopologicalSpace X] [hT2 : T2Space X] [TopologicalSpace Y]
    {t' : TopologicalSpace X} (hle : t' ≤ t)
    {K : Set X} (hK : @IsCompact X t' K) {f : X → Y}
    (hf : @Continuous X Y t' _ f) : @ContinuousOn X Y t _ f K := by
  apply (@continuousOn_iff_isClosed X Y t _ f K).2
  intro s hs
  have hC : @IsCompact X t' (K ∩ f ⁻¹' s) :=
    hK.inter_right (hs.preimage hf)
  have hC' : @IsCompact X t (K ∩ f ⁻¹' s) := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t (K ∩ f ⁻¹' s) id hC (continuous_id_of_le hle))
  exact ⟨K ∩ f ⁻¹' s, @IsCompact.isClosed X t hT2 _ hC',
    by ext x; simp [and_comm]⟩

theorem exists_compact_continuousOn {X Y : Type*}
    [t : TopologicalSpace X] [hPolish : PolishSpace X]
    [m : MeasurableSpace X] [hBorel : BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨t', hle, hfc, hP'⟩ := hf.exists_continuous
  have hB' : @BorelSpace X t' m := by
    constructor
    exact hBorel.measurable_eq.trans
      (MeasureTheory.borel_eq_borel_of_le hP' hPolish hle).symm
  let : TopologicalSpace X := t'
  let : PolishSpace X := hP'
  let : BorelSpace X := hB'
  obtain ⟨K, -, hK, hsmall⟩ :=
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set X)).exists_isCompact_sdiff_lt
      (measure_ne_top μ Set.univ) hε
  have hKold : @IsCompact X t K := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t K id hK (continuous_id_of_le hle))
  refine ⟨K, hKold, ?_, ?_⟩
  · simpa only [← compl_eq_univ_sdiff] using hsmall
  · exact @continuousOn_of_finer_compact X Y t inferInstance _ t' hle K hK f hfc

theorem exists_compact_forall_continuousOn {X ι : Type*} {Y : ι → Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [Countable ι]
    [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
    [∀ i, OpensMeasurableSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ∀ i, X → Y i)
    (hf : ∀ i, Measurable (f i)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ∀ i, ContinuousOn (f i) K := by
  have hjoint : Measurable (fun x i => f i x) := Measurable.of_eval hf
  obtain ⟨K, hK, hsmall, hcont⟩ := exists_compact_continuousOn μ hjoint hε
  exact ⟨K, hK, hsmall, continuousOn_pi.mp hcont⟩

end Invariant233.SimultaneousLusin

end OAI
