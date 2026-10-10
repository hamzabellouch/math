import OAI.Probability.SLE.Geometry.CanonicalRawTerminal
import OAI.Probability.SLE.Mass.RestartRandomMassTesting

namespace OAI

/-! The fixed raw terminal functional has the exact Green mean under the
driver law. Strong Markov then allows arbitrary stopped-past spatial weights
in the fresh terminal mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.raw_terminal_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, R.terminal (sourceDriverPath B hBc ω) = C.rational.terminal ω) :
    (P.map (sourceDriverPath B hBc)).bind R.terminal = initialGreenMeasure κ := by
  have hp : Measurable (sourceDriverPath B hBc) := source_path_measurable _
    (fun t => hBm.comp (measurable_const.prodMk measurable_id))
  calc
    _ = P.bind (fun ω => R.terminal (sourceDriverPath B hBc ω)) := by
      unfold Measure.bind
      rw [Measure.map_map R.terminal_measurable hp]
      rfl
    _ = P.bind C.rational.terminal := Measure.bind_congr_right he
    _ = initialGreenMeasure κ := C.rational.mean

theorem CanonicalMass.restarted_raw_terminal_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0))) :
    P.bind (fun ω => R.terminal (sourceRestartDriverPath B hc τ ω))=initialGreenMeasure κ := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  have hY : Measurable (sourceRestartDriverPath B hc τ) := source_path_measurable _
    (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  have hlaw : P.map (sourceRestartDriverPath B hc τ)=P.map (sourceDriverPath B hc) := by
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      source_restart_continuous_driver_law hB hm hc τ hτ (A := univ) MeasurableSet.univ
  calc
    _ = (P.map (sourceRestartDriverPath B hc τ)).bind R.terminal := by
      unfold Measure.bind
      rw [Measure.map_map R.terminal_measurable hY]
      rfl
    _ = initialGreenMeasure κ := by rw [hlaw,C.raw_terminal_mean hc R he]


theorem CanonicalMass.fresh_terminal_random_test
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, R.terminal (sourceDriverPath B hBc ω) = C.rational.terminal ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (f : Ω × upperHalfPlane → ℝ≥0∞)
    (hf : Measurable[hτ.measurableSpace.prod inferInstance] f) :
    (∫⁻ ω, ∫⁻ z, f (ω,z) ∂(R.terminal (sourceRestartDriverPath B hBc τ ω)) ∂P) =
      ∫⁻ ω, ∫⁻ z, f (ω,z) ∂initialGreenMeasure κ ∂P := by
  have hm (t : ℝ≥0) : Measurable (B t) :=
    hBm.comp (measurable_const.prodMk measurable_id)
  have hp : Measurable (sourceDriverPath B hBc) := source_path_measurable _ hm
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hBc)) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hY : Measurable (sourceRestartDriverPath B hBc τ) :=
    source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hBc (stopping_time_measurable_nnreal hτ)))
  have h := restart_random_mass_test P (P.map (sourceDriverPath B hBc))
    hτ.measurableSpace hτ.measurableSpace_le (sourceRestartDriverPath B hBc τ) hY
    (fun A hA => source_restart_continuous_driver_law hB hm hBc τ hτ hA)
    R.terminal R.terminal_measurable (fun p => (R.terminal_radon p).2) f hf
  rwa [C.raw_terminal_mean hBc R he] at h

end SLEExactGauge.Multipoint

end

end OAI
