import OAI.Probability.SLE.Loewner.RawRestartAdaptation
import OAI.Probability.SLE.Loewner.RawTerminalExhaustion

namespace OAI

/-! One fixed raw canonical mass works at every finite Brownian restart.
The finite process is progressive in the shifted past and locally exhausts
its own terminal measure on one full event for each restart. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology CompactlySupported NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance rawRestartCanonicalMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawRestartCanonicalBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.exists_raw_restarted_canonical
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    ∃ R : RawCanonicalMass,
      (∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hBc ω)=C.process t ω) ∧
        R.terminal (sourceDriverPath B hBc ω)=C.rational.terminal ω) ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτ : IsStoppingTime (Filtration.natural B (fun t =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
          (fun ω => (τ ω : WithTop ℝ≥0))),
        IsProgressive (shiftedStoppingFiltration hτ)
          (fun t ω => R.process t (sourceRestartDriverPath B hBc τ ω)) ∧
        ∀ᵐ ω ∂P,
          R.process 0 (sourceRestartDriverPath B hBc τ ω)=0 ∧
          Monotone (fun t => R.process t (sourceRestartDriverPath B hBc τ ω)) ∧
          (∀ f : C_c(upperHalfPlane,ℝ), Continuous
            (fun t => ∫ z, f z ∂(R.process t (sourceRestartDriverPath B hBc τ ω)))) ∧
          (∀ t, R.process t (sourceRestartDriverPath B hBc τ ω) ≤
            R.terminal (sourceRestartDriverPath B hBc τ ω)) ∧
          ∀ K : Set upperHalfPlane, IsCompact K → Tendsto
            (fun t : ℝ≥0 => (R.terminal (sourceRestartDriverPath B hBc τ ω)-
              R.process t (sourceRestartDriverPath B hBc τ ω)) K) atTop (𝓝 0) := by
  obtain ⟨N,hNp,hNr,hNn,he,hfresh⟩ := C.exists_raw_with_restarted_paths hB hBc
  let R : RawCanonicalMass := ⟨N,rawTerminalMass N,hNp,hNr,
    rawTerminalMass_measurable N hNp hNr,rawTerminalMass_radon N,hNn⟩
  have hterm := C.rawTerminal_realizes hBc N he
  obtain ⟨hE,hEf,hEg⟩ := C.raw_terminal_good_set hBc N hNp hNr he
  refine ⟨R,?_,?_⟩
  · filter_upwards [he,hterm] with ω hf ht
    exact ⟨hf,ht⟩
  · intro τ hτ
    obtain ⟨hprog,hpath⟩ := hfresh τ hτ
    refine ⟨hprog,?_⟩
    have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
    have hset := sourceRestart_mem_full_driver_set hB hm hBc τ hτ _ hE hEf
    filter_upwards [hpath,hset] with ω hp hs
    obtain ⟨hdom,hex⟩ := hEg _ hs hp.2.1
    exact ⟨hp.1,hp.2.1,hp.2.2,hdom,hex⟩

end SLEExactGauge.Multipoint

end

end OAI
