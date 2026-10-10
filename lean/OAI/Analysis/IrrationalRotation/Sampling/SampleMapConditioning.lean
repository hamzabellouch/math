import OAI.Analysis.IrrationalRotation.Analysis.ObservationConditioning

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Invariant233.SampleMapConditioning

variable {Ω Ω' A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A]

theorem condExp_observation_comp_measurePreserving
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {X : Ω' → A} (hX : Measurable X) {f : Ω' → ℝ} (hf : Integrable f ν) :
    μ[f ∘ g | MeasurableSpace.comap (X ∘ g) inferInstance] =ᵐ[μ]
      (ν[f | MeasurableSpace.comap X inferInstance]) ∘ g := by
  have hXm : AEMeasurable X (μ.map g) := by
    rw [hg.map_eq]
    exact hX.aemeasurable
  have hfm : AEMeasurable f (μ.map g) := by
    rw [hg.map_eq]
    exact hf.aemeasurable
  have hk : condDistrib f X ν =ᵐ[μ.map (X ∘ g)]
      condDistrib (f ∘ g) (X ∘ g) μ := by
    simpa only [hg.map_eq] using
      (condDistrib_map hXm hfm hg.measurable.aemeasurable)
  have hk' := ae_of_ae_map ((hX.comp hg.measurable).aemeasurable) hk
  have hsrc := condExp_ae_eq_integral_condDistrib'
    (hX.comp hg.measurable) (hg.integrable_comp_of_integrable hf)
  have hdst := hg.quasiMeasurePreserving.ae
    (condExp_ae_eq_integral_condDistrib' hX hf)
  filter_upwards [hsrc, hdst, hk'] with ω hω hν hκ
  simp only [Function.comp_apply] at hω hν hκ ⊢
  rw [hω, hν, hκ]

theorem condExp_preimage_indicator
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {X : Ω' → A} (hX : Measurable X) {s : Set Ω'} (hs : MeasurableSet s) :
    μ[(g ⁻¹' s).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (X ∘ g) inferInstance] =ᵐ[μ]
      (ν[s.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance]) ∘ g := by
  have hcomp : (s.indicator (fun _ => (1 : ℝ))) ∘ g =
      (g ⁻¹' s).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : g ω ∈ s <;> simp [h]
  simpa only [hcomp] using
    condExp_observation_comp_measurePreserving μ ν hg hX
      ((integrable_const (1 : ℝ)).indicator hs)

theorem condExp_preimage_indicator_le
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {X : Ω' → A} (hX : Measurable X) {s : Set Ω'} (hs : MeasurableSet s)
    (b : ℝ) (hb : ∀ᵐ z ∂ν,
      (ν[s.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance]) z ≤ b) :
    ∀ᵐ ω ∂μ, (μ[(g ⁻¹' s).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (X ∘ g) inferInstance]) ω ≤ b := by
  filter_upwards [condExp_preimage_indicator μ ν hg hX hs,
    hg.quasiMeasurePreserving.ae hb] with ω heq hbound
  exact heq.trans_le hbound

theorem condExp_preimage_indicator_le_countable {I : Type*} [Countable I]
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {X : Ω' → A} (hX : Measurable X) (s : I → Set Ω')
    (hs : ∀ i, MeasurableSet (s i)) (b : I → ℝ)
    (hb : ∀ᵐ z ∂ν, ∀ i, (ν[(s i).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance]) z ≤ b i) :
    ∀ᵐ ω ∂μ, ∀ i, (μ[(g ⁻¹' s i).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (X ∘ g) inferInstance]) ω ≤ b i := by
  apply ae_all_iff.mpr
  intro i
  exact condExp_preimage_indicator_le μ ν hg hX (hs i) (b i)
    (hb.mono (fun z hz => hz i))

theorem condExp_preimage_indicator_le_countable_on {I : Type*} [Countable I]
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {X : Ω' → A} (hX : Measurable X) (s : I → Set Ω')
    (hs : ∀ i, MeasurableSet (s i)) (b : I → ℝ) (q : I → Prop)
    (hb : ∀ᵐ z ∂ν, ∀ i, q i → (ν[(s i).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance]) z ≤ b i) :
    ∀ᵐ ω ∂μ, ∀ i, q i → (μ[(g ⁻¹' s i).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (X ∘ g) inferInstance]) ω ≤ b i := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro hi
  exact condExp_preimage_indicator_le μ ν hg hX (hs i) (b i)
    (hb.mono (fun z hz => hz i hi))

theorem condExp_preimage_indicator_of_observation_ae
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν)
    {X : Ω' → A} (hX : Measurable X) {Y : Ω → A} (hY : Measurable Y)
    (hXY : (X ∘ g) =ᵐ[μ] Y) {s : Set Ω'} (hs : MeasurableSet s) :
    μ[(g ⁻¹' s).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap Y inferInstance] =ᵐ[μ]
      (ν[s.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance]) ∘ g := by
  exact (ObservationConditioning.condExp_comap_congr_ae μ
    (hX.comp hg.measurable) hY hXY _).symm.trans
    (condExp_preimage_indicator μ ν hg hX hs)

end Invariant233.SampleMapConditioning

end OAI
