import OAI.Probability.SLE.Loewner.StoppedInversePaths

namespace OAI

/-! Local terminal exhaustion survives the stopped conformal weighting.
The pulled-back compact need not stay away from the real boundary: finite
terminal weighted mass is the domination used for the limit. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge

local instance stoppedExhaustionLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

lemma weightedImageMass_add
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (μ ν : Measure upperHalfPlane) :
    weightedImageMass J w (μ+ν) = weightedImageMass J w μ + weightedImageMass J w ν := by
  simp only [weightedImageMass,withDensity_add_measure]
  exact Measure.map_add _ _ hJ

lemma weightedImageMass_sub
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) {μ ν : Measure upperHalfPlane}
    [SigmaFinite μ] (hle : μ ≤ ν)
    [IsFiniteMeasureOnCompacts (weightedImageMass J w ν)] :
    weightedImageMass J w (ν-μ) = weightedImageMass J w ν-weightedImageMass J w μ := by
  let := weightedImageMass_finite_on_compacts J hJ w hle
  apply (Measure.add_left_inj (weightedImageMass J w μ) _ _).mp
  calc
    weightedImageMass J w (ν-μ)+weightedImageMass J w μ = weightedImageMass J w ν := by
      rw [← weightedImageMass_add J hJ w,sigmaFinite_sub_add_cancel_of_le hle]
    _ = (weightedImageMass J w ν-weightedImageMass J w μ)+weightedImageMass J w μ :=
      (sigmaFinite_sub_add_cancel_of_le (weightedImageMass_mono J hJ w hle)).symm

lemma weightedImageMass_terminal_exhaustion
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) [ν.Regular]
    (hNr : ∀ t, (N t).Regular) (hdom : ∀ t, N t ≤ ν)
    (hlim : ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0))
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (hw : Measurable w)
    [IsFiniteMeasureOnCompacts (weightedImageMass J w ν)] :
    ∀ K : Set upperHalfPlane, IsCompact K → Tendsto
      (fun t : ℝ≥0 => (weightedImageMass J w ν-weightedImageMass J w (N t)) K)
      atTop (𝓝 0) := by
  intro K hK
  let g : upperHalfPlane → ℝ≥0∞ := (J ⁻¹' K).indicator w
  have hg : Measurable g := hw.indicator (hJ hK.measurableSet)
  have hfin : (∫⁻ z, g z ∂ν) ≠ ∞ := by
    rw [← weightedImageMass_apply J hJ w ν K hK.measurableSet]
    exact hK.measure_lt_top.ne
  have he (t : ℝ≥0) :
      (weightedImageMass J w ν-weightedImageMass J w (N t)) K =
        ∫⁻ z, g z ∂(ν-N t) := by
    let := hNr t
    rw [← weightedImageMass_sub J hJ w (hdom t),
      weightedImageMass_apply J hJ w (ν-N t) K hK.measurableSet]
  simpa only [he] using remaining_lintegral_tendsto_zero ν N hNr hdom hlim g hg hfin

namespace Multipoint

local instance stoppedExhaustionDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance stoppedExhaustionDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
  (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (τ : Ω → ℝ≥0) (hc : ∀ ω, Continuous (fun t => B t ω)) (R : RawCanonicalMass)
  (hm : ∀ t, Measurable (B t))
  (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0)))

include hm hτ in
theorem stoppedFreshMass_terminal_exhaustion
    {P : Measure Ω} (hκ : 0 < κ)
    (hdom : ∀ᵐ ω ∂P, ∀ t, R.process t (sourceRestartDriverPath B hc τ ω) ≤
      R.terminal (sourceRestartDriverPath B hc τ ω))
    (hlim : ∀ᵐ ω ∂P, ∀ K : Set upperHalfPlane, IsCompact K → Tendsto
      (fun t : ℝ≥0 => (R.terminal (sourceRestartDriverPath B hc τ ω)-
        R.process t (sourceRestartDriverPath B hc τ ω)) K) atTop (𝓝 0))
    (hfin : ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω)) :
    ∀ᵐ ω ∂P, ∀ K : Set upperHalfPlane, IsCompact K → Tendsto
      (fun t : ℝ≥0 => (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω-
        stoppedFreshMass B κ γ G F hw τ hc R t ω) K) atTop (𝓝 0) := by
  have hJ := stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ
  have hW := stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ
  filter_upwards [hdom,hlim,hfin] with ω hd hl hf
  let J := stoppedMassPoint B κ γ G F hw τ ω
  let w := stoppedMassWeight B κ F τ ω
  have hpair : @Measurable upperHalfPlane (Ω × upperHalfPlane) inferInstance
      (hτ.measurableSpace.prod inferInstance) (fun z => (ω,z)) :=
    @measurable_prodMk_left Ω upperHalfPlane hτ.measurableSpace inferInstance ω
  have hJm : Measurable J :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) upperHalfPlane
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassPoint B κ γ G F hw τ p.1 p.2) (fun z => (ω,z)) hJ hpair
  have hwm : Measurable w :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) ℝ≥0∞
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassWeight B κ F τ p.1 p.2) (fun z => (ω,z)) hW hpair
  let N := fun t => R.process t (sourceRestartDriverPath B hc τ ω)
  let ν := R.terminal (sourceRestartDriverPath B hc τ ω)
  change ∀ K : Set upperHalfPlane, IsCompact K → Tendsto
    (fun t : ℝ≥0 => (weightedImageMass J w ν-weightedImageMass J w (N t)) K) atTop (𝓝 0)
  exact @weightedImageMass_terminal_exhaustion N ν
    (R.terminal_radon (sourceRestartDriverPath B hc τ ω)).1
    (fun t => (R.radon t _).1) hd hl J hJm w hwm hf

end Multipoint
end SLEExactGauge

end

end OAI
