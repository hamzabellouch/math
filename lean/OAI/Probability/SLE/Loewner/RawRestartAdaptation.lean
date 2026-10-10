import OAI.Probability.SLE.Mass.RawMassPathLaw
import OAI.Probability.SLE.Stochastic.ShiftedStoppingFiltration

namespace OAI

/-! The fixed raw mass applied to the fresh driver is progressive in the
original filtration shifted by the stopping time. Its continuous increasing
paths are transferred on the explicit measurable good set. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology CompactlySupported NNReal ENNReal

namespace SLEExactGauge

local instance rawRestartDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawRestartDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma driverPath_measurable_past_of_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (Y : Ω → C(ℝ≥0,ℝ)) (hY : Adapted ℱ (fun t ω => Y ω t)) (t : ℝ≥0) :
    Measurable[ℱ t,driverPathFiltration t] Y := by
  rw [driverPathFiltration,Filtration.natural_eq_comap]
  let : MeasurableSpace Ω := ℱ t
  apply measurable_comap_iff.mpr
  apply measurable_pi_iff.mpr
  intro s
  exact (hY s).mono (ℱ.mono s.property) le_rfl

theorem raw_process_comp_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (Y : Ω → C(ℝ≥0,ℝ)) (hY : Adapted ℱ (fun t ω => Y ω t))
    (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (hR : IsProgressive driverPathFiltration R) :
    IsProgressive ℱ (fun t ω => R t (Y ω)) := by
  intro t
  exact (hR t).comp (measurable_fst.prodMk
    ((driverPath_measurable_past_of_adapted ℱ Y hY t).comp measurable_snd))

lemma sourceRestartDriverPath_shifted_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Adapted (shiftedStoppingFiltration hτ)
      (fun t ω => sourceRestartDriverPath B hc τ ω t) := by
  have hX := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc
  have hs := shiftedStopping_adapted hτ B hX
  have h0 : StronglyMeasurable[(shiftedStoppingFiltration hτ) 0]
      (fun ω => B (τ ω) ω) := by
    simpa only [add_zero] using hs 0
  intro t
  have hd := ((hs t).sub (h0.mono ((shiftedStoppingFiltration hτ).mono (show 0 ≤ t from zero_le)))).measurable
  exact hd

theorem sourceRestart_raw_process_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (hR : IsProgressive driverPathFiltration R) :
    IsProgressive (shiftedStoppingFiltration hτ)
      (fun t ω => R t (sourceRestartDriverPath B hc τ ω)) :=
  raw_process_comp_progressive _ _ (sourceRestartDriverPath_shifted_adapted B hm hc τ hτ) R hR

theorem sourceRestart_mem_full_driver_set
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hfull : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p ∈ E) :
    ∀ᵐ ω ∂P, sourceRestartDriverPath B hc τ ω ∈ E := by
  have hY : Measurable (sourceRestartDriverPath B hc τ) := source_path_measurable _
    (fun t => (sourceRestartDriverPath_shifted_adapted B hm hc τ hτ).measurable (i := t))
  have hlaw : P.map (sourceRestartDriverPath B hc τ)=P.map (sourceDriverPath B hc) := by
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      source_restart_continuous_driver_law hB hm hc τ hτ (MeasurableSet.univ : MeasurableSet[hτ.measurableSpace] univ)
  apply (ae_map_iff hY.aemeasurable hE).mp
  rwa [hlaw]

namespace Multipoint

theorem CanonicalMass.exists_raw_with_restarted_paths
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    ∃ R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane,
      IsProgressive driverPathFiltration R ∧
      (∀ t p, (R t p).Regular ∧ IsFiniteMeasureOnCompacts (R t p)) ∧
      (∀ t p r, (∀ s ≤ t, p s=r s) → R t p=R t r) ∧
      (∀ᵐ ω ∂P, ∀ t, R t (sourceDriverPath B hBc ω)=C.process t ω) ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτ : IsStoppingTime (Filtration.natural B (fun t =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
          (fun ω => (τ ω : WithTop ℝ≥0))),
        IsProgressive (shiftedStoppingFiltration hτ)
          (fun t ω => R t (sourceRestartDriverPath B hBc τ ω)) ∧
        ∀ᵐ ω ∂P, R 0 (sourceRestartDriverPath B hBc τ ω)=0 ∧
          Monotone (fun t => R t (sourceRestartDriverPath B hBc τ ω)) ∧
          ∀ f : C_c(upperHalfPlane,ℝ),
            Continuous (fun t => ∫ z, f z ∂(R t (sourceRestartDriverPath B hBc τ ω))) := by
  obtain ⟨R,E,hRp,hRr,hRn,hE,hfull,hgood,he⟩ := C.exists_raw_nonanticipating_with_good_set hBc
  refine ⟨R,hRp,hRr,hRn,he,?_⟩
  intro τ hτ
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  refine ⟨sourceRestart_raw_process_progressive B hm hBc τ hτ R hRp,?_⟩
  filter_upwards [sourceRestart_mem_full_driver_set hB hm hBc τ hτ E hE hfull] with ω hω
  exact hgood _ hω

end Multipoint
end SLEExactGauge

end

end OAI
