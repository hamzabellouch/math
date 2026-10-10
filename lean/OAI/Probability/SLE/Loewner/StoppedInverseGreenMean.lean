import OAI.Probability.SLE.Mass.StoppedInverseMass
import OAI.Probability.SLE.Geometry.RestartHalfPlaneGreen
import OAI.Probability.SLE.Loewner.FreshCapacityWitness

namespace OAI

/-! The actual weighted fresh terminal mass has exactly the same stopped
Green kernel as the remaining original mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun t =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (hFresh : ∀ᵐ ω ∂P, ∃ (β : ℝ≥0 → ℂ) (G' F' : ℝ≥0 → ℂ → ℂ),
    IsCapacityTwoWitness (fun t => Real.sqrt κ*B (τ ω+t) ω-Real.sqrt κ*B (τ ω) ω) β G' F')

include C hB hc hκ F hw τ hτ R he hFresh in
theorem CanonicalMass.stoppedFreshTerminalMass_green_test
    (f : Ω × upperHalfPlane → ℝ≥0∞)
    (hf : Measurable[hτ.measurableSpace.prod inferInstance] f) :
    (∫⁻ ω, ∫⁻ x, f (ω,x) ∂(stoppedFreshTerminalMass B κ γ G F hw τ hc R ω) ∂P) =
      ∫⁻ ω, ∫⁻ x, f (ω,x) ∂halfPlaneGreenMeasure κ B γ G (τ ω) ω ∂P := by
  rw [C.stoppedFreshTerminalMass_test B κ γ G F hw τ
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc hτ hB hκ R he f hf]
  apply lintegral_congr_ae
  filter_upwards [hFresh] with ω hω
  obtain ⟨β,G',F',hb⟩ := hω
  exact restart_halfPlane_green_test (hw ω) ((hc ω).const_mul _) (τ ω) hb hκ
    (fun x => f (ω,x))

omit [IsProbabilityMeasure P] in
lemma past_rectangle_lintegral
    (μ : Ω → Measure upperHalfPlane) (E : Set Ω) (hE : MeasurableSet E)
    (A : Set upperHalfPlane) (hA : MeasurableSet A) :
    (∫⁻ ω, ∫⁻ z, (E ×ˢ A).indicator (fun _ => (1:ℝ≥0∞)) (ω,z) ∂μ ω ∂P) =
      ∫⁻ ω in E, μ ω A ∂P := by
  rw [← lintegral_indicator hE]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ E
  · have hsec : (fun z => (E ×ˢ A).indicator (fun _ => (1:ℝ≥0∞)) (ω,z)) =
        A.indicator (fun _ => 1) := by
      funext z
      simp only [Set.indicator,Set.mem_prod,hω,true_and]
    rw [hsec,lintegral_indicator hA,lintegral_one]
    simp only [Set.indicator_of_mem hω,Measure.restrict_apply_univ]
  · have hsec : (fun z => (E ×ˢ A).indicator (fun _ => (1:ℝ≥0∞)) (ω,z)) = 0 := by
      funext z
      simp only [Set.indicator,Set.mem_prod,hω,false_and,ite_false,Pi.zero_apply]
    rw [hsec]
    change (∫⁻ z, (0:ℝ≥0∞) ∂μ ω) = _
    simp only [lintegral_zero,Set.indicator_of_notMem hω]

include C hB hc hκ F hw τ hτ R he hFresh in
theorem CanonicalMass.stoppedFreshTerminalMass_kernel
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E) :
    (P.restrict E).bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R) =
      (P.restrict E).bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω) ω) := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  have hμ := stoppedFreshTerminalMass_measurable B κ γ G F hw τ hm hc hτ hκ R
  have hν : Measurable (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω) ω) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
    simp only [halfPlaneGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
      withDensity_apply _ hAI]
    exact (actual_greenDensity_random_time_joint_measurable hBm hc κ γ G F hw τ
      (stopping_time_measurable_nnreal hτ)).ennreal_ofReal.lintegral_prod_right'
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA hμ.aemeasurable,Measure.bind_apply hA hν.aemeasurable]
  have ht := C.stoppedFreshTerminalMass_green_test hB hc hκ F hw τ hτ R he hFresh
    ((E ×ˢ A).indicator (fun _ => 1)) (measurable_const.indicator (hE.prod hA))
  rw [past_rectangle_lintegral _ E (hτ.measurableSpace_le E hE) A hA,
    past_rectangle_lintegral _ E (hτ.measurableSpace_le E hE) A hA] at ht
  exact ht

include C hB hc hκ F hw τ hτ R he in
theorem CanonicalMass.stoppedFreshTerminalMass_published_kernel
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E) :
    (P.restrict E).bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R) =
      (P.restrict E).bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω) ω) := by
  exact C.stoppedFreshTerminalMass_kernel hB hc hκ F hw τ hτ R he
    (fresh_capacity_witness_exists hB
      (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc hpublished τ hτ) E hE

end SLEExactGauge.Multipoint

end

end OAI
