import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.TwoPoint

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SharpIntegralFillings
lemma exists_closed_large_continuousOn
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {f : A → B} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set A, IsClosed K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  let I := countableBasis B
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε I
  have H (i : I) : ∃ U F : Set A,
      f ⁻¹' (i : Set B) ⊆ U ∧ F ⊆ f ⁻¹' (i : Set B) ∧
      IsOpen U ∧ IsClosed F ∧ μ (U \ F) < δ i := by
    let S := f ⁻¹' (i : Set B)
    have hS : MeasurableSet S := hf (isOpen_of_mem_countableBasis i.property).measurableSet
    have hδi : δ i / 2 ≠ 0 := (ENNReal.half_pos (hδ i).ne').ne'
    obtain ⟨U,hSU,hU,_,hμU⟩ := hS.exists_isOpen_sdiff_lt (measure_ne_top μ S) hδi
    obtain ⟨F,hFS,hF,hμF⟩ := hS.exists_isClosed_sdiff_lt (measure_ne_top μ S) hδi
    refine ⟨U,F,hSU,hFS,hU,hF,?_⟩
    calc μ (U \ F) ≤ μ ((U \ S) ∪ (S \ F)) := by
          apply measure_mono
          intro x hx
          by_cases hxs : x ∈ S
          · exact Or.inr ⟨hxs,hx.2⟩
          · exact Or.inl ⟨hx.1,hxs⟩
      _ ≤ μ (U \ S) + μ (S \ F) := measure_union_le _ _
      _ < δ i / 2 + δ i / 2 := ENNReal.add_lt_add hμU hμF
      _ = δ i := ENNReal.add_halves _
  choose U F hSU hFS hU hF hμ using H
  let K : Set A := (⋃ i : I, U i \ F i)ᶜ
  refine ⟨K, (isOpen_iUnion (fun i => (hU i).sdiff (hF i))).isClosed_compl, ?_, ?_⟩
  · calc μ Kᶜ = μ (⋃ i : I, U i \ F i) := by simp [K]
      _ ≤ ∑' i : I, μ (U i \ F i) := measure_iUnion_le _
      _ ≤ ∑' i : I, δ i := ENNReal.tsum_le_tsum (fun i => (hμ i).le)
      _ < ε := hδsum
  · apply (isBasis_countableBasis B).continuousOn_iff.mpr
    intro V hV
    let i : I := ⟨V,hV⟩
    refine ⟨U i,hU i,?_⟩
    ext x
    constructor
    · rintro ⟨hx,hxK⟩
      exact ⟨hSU i hx,hxK⟩
    · rintro ⟨hxU,hxK⟩
      have hxF : x ∈ F i := by
        by_contra h
        exact hxK (mem_iUnion.mpr ⟨i,hxU,h⟩)
      exact ⟨hFS i hxF,hxK⟩

end SharpIntegralFillings

namespace SharpIntegralFillings
open Metric

lemma exists_large_continuousOn_uniformly
    {A B : Type*} [TopologicalSpace A] [PseudoMetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A)
    {s : Set A} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {f : A → B} (hf : Measurable f) {u : ℕ → A → ℝ}
    (hu : ∀ n, Measurable (u n))
    (hc : ∀ᵐ x ∂μ.restrict s, Tendsto (fun n => u n x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ContinuousOn f t ∧ TendstoUniformlyOn u (fun _ => 0) atTop t := by
  let ν := μ.restrict s
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hsf.lt_top⟩
  obtain ⟨K,hK,hμK,hcf⟩ := exists_closed_large_continuousOn ν hf
    (show ENNReal.ofReal (ε/2) ≠ 0 from (ENNReal.ofReal_pos.mpr (half_pos hε)).ne')
  obtain ⟨e,he,hμe,hue⟩ := tendstoUniformlyOn_of_ae_tendsto'
    (fun n => (hu n).stronglyMeasurable) stronglyMeasurable_const hc
    (ENNReal.ofReal_pos.mpr (half_pos hε))
  let t := s ∩ (K \ e)
  refine ⟨t,inter_subset_left,hs.inter (hK.measurableSet.diff he),?_,
    hcf.mono (fun _ h => h.2.1),hue.mono (fun _ h => h.2.2)⟩
  calc μ (s \ t) = ν (Kᶜ ∪ e) := by
        rw [Measure.restrict_apply (hK.measurableSet.compl.union he)]
        congr 1
        ext x
        simp only [t,Set.mem_sdiff,mem_inter_iff,mem_union,mem_compl_iff]
        tauto
    _ ≤ ν Kᶜ + ν e := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hμK.le hμe
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_large_twoPointMetricDifferential
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ x ∈ t, HasTwoPointMetricDifferential f (metricSeminorm f x) t x := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  obtain ⟨t,hts,ht,hμt,hct,htu⟩ := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x j => metricSeminorm f x (denseSeq E j)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun n => measurable_metricErrorModulus hf (r n)) hc hε
  refine ⟨t,hts,ht,hμt,?_⟩
  intro x hx
  apply hasTwoPointMetricDifferential_of_uniformModulus hf _ hr htu
  intro j
  exact (continuousOn_pi.1 hct j) x hx

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
