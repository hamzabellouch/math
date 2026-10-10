import OAI.Probability.SLE.Loewner.RawRestartCanonical
import OAI.Probability.SLE.Loewner.StoppedInverseTerminalBound
import OAI.Probability.SLE.Mass.DominatedMassTestExhaustion

namespace OAI

/-! The finite fresh mass transported by the actual stopped inverse chart.
The same raw functional is used for all finite stopping times. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge

local instance stoppedInversePathsLocallyCompact : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma weightedImageMass_mono
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) {μ ν : Measure upperHalfPlane} (hle : μ ≤ ν) :
    weightedImageMass J w μ ≤ weightedImageMass J w ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [weightedImageMass_apply J hJ w μ A hA,weightedImageMass_apply J hJ w ν A hA]
  exact lintegral_mono' hle le_rfl

lemma weightedImageMass_zero (J : upperHalfPlane → upperHalfPlane)
    (w : upperHalfPlane → ℝ≥0∞) : weightedImageMass J w 0=0 := by
  simp only [weightedImageMass,withDensity_zero_left,Measure.map_zero]

lemma weightedImageMass_finite_on_compacts
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) {μ ν : Measure upperHalfPlane}
    (hle : μ ≤ ν) [IsFiniteMeasureOnCompacts (weightedImageMass J w ν)] :
    IsFiniteMeasureOnCompacts (weightedImageMass J w μ) :=
  ⟨fun K hK => lt_of_le_of_lt (weightedImageMass_mono J hJ w hle K) hK.measure_lt_top⟩

lemma weightedImageMass_positive_test_continuous
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) [ν.Regular]
    (hdom : ∀ t, N t ≤ ν)
    (hc : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t))
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (hw : Measurable w)
    [IsFiniteMeasureOnCompacts (weightedImageMass J w ν)]
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    Continuous (fun t => ∫ z, f z ∂(weightedImageMass J w (N t))) := by
  let g := fun z => w z * ENNReal.ofReal (f (J z))
  have hg : Measurable g := hw.mul (f.continuous.measurable.comp hJ).ennreal_ofReal
  have hν : (∫⁻ z, g z ∂ν) ≠ ∞ := by
    rw [← weightedImageMass_lintegral J hJ w hw ν (fun z => ENNReal.ofReal (f z))
      f.continuous.measurable.ennreal_ofReal]
    rw [← ofReal_integral_eq_lintegral_ofReal f.integrable (ae_of_all _ hf)]
    exact ENNReal.ofReal_ne_top
  have hgc := continuous_lintegral_of_radon_domination N ν hdom hc g hg hν
  have hfinite (t : ℝ≥0) : (∫⁻ z, g z ∂N t) ≠ ∞ :=
    ne_top_of_le_ne_top hν (lintegral_mono' (hdom t) le_rfl)
  have hreal : Continuous (fun t => (∫⁻ z, g z ∂N t).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : ContinuousAt (fun u : ℝ≥0 => ∫⁻ z, g z ∂N u) t := hgc.continuousAt
    exact ContinuousAt.comp (f := fun u : ℝ≥0 => ∫⁻ z, g z ∂N u) (x := t)
      (ENNReal.continuousAt_toReal (hfinite t)) ht
  have he (t : ℝ≥0) : (∫ z, f z ∂(weightedImageMass J w (N t))) = (∫⁻ z, g z ∂N t).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) f.continuous.measurable.aestronglyMeasurable,
      weightedImageMass_lintegral J hJ w hw (N t) (fun z => ENNReal.ofReal (f z))
        f.continuous.measurable.ennreal_ofReal]
  simpa only [he] using hreal


lemma positive_test_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω] (N : Ω → Measure upperHalfPlane) (hN : Measurable N)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    Measurable (fun ω => ∫ z, f z ∂N ω) := by
  have h := ENNReal.measurable_toReal.comp
    ((Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp hN)
  have he (ω : Ω) : (∫ z, f z ∂N ω) = (∫⁻ z, ENNReal.ofReal (f z) ∂N ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) f.continuous.measurable.aestronglyMeasurable
  convert h using 1
  funext ω
  exact he ω

structure PositiveMassPaths (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) : Prop where
  zero : N 0=0
  monotone : Monotone N
  dominated : ∀ t, N t ≤ ν
  radon : ∀ t, (N t).Regular ∧ IsFiniteMeasureOnCompacts (N t)
  continuous_tests : ∀ f : C_c(upperHalfPlane,ℝ), (∀ z, 0 ≤ f z) →
    Continuous (fun t => ∫ z, f z ∂N t)

lemma weightedImageMass_positive_paths
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) [ν.Regular]
    (hz : N 0=0) (hm : Monotone N) (hdom : ∀ t, N t ≤ ν)
    (hc : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t))
    (J : upperHalfPlane → upperHalfPlane) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (hw : Measurable w)
    [IsFiniteMeasureOnCompacts (weightedImageMass J w ν)] :
    PositiveMassPaths (fun t => weightedImageMass J w (N t)) (weightedImageMass J w ν) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hz,weightedImageMass_zero]
  · intro s t hst
    exact weightedImageMass_mono J hJ w (hm hst)
  · intro t
    exact weightedImageMass_mono J hJ w (hdom t)
  · intro t
    let := weightedImageMass_finite_on_compacts J hJ w (hdom t)
    exact ⟨inferInstance,inferInstance⟩
  · intro f hf
    exact weightedImageMass_positive_test_continuous N ν hdom hc J hJ w hw f hf

namespace Multipoint

local instance stoppedInversePathsDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance stoppedInversePathsDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
  (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (τ : Ω → ℝ≥0) (hc : ∀ ω, Continuous (fun t => B t ω)) (R : RawCanonicalMass)

def stoppedFreshMass (t : ℝ≥0) (ω : Ω) : Measure upperHalfPlane :=
  weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω) (stoppedMassWeight B κ F τ ω)
    (R.process t (sourceRestartDriverPath B hc τ ω))

variable (hm : ∀ t, Measurable (B t))
  (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0)))

include hm hτ in
theorem stoppedFreshMass_adapted (hκ : 0 < κ) :
    Adapted (shiftedStoppingFiltration hτ) (stoppedFreshMass B κ γ G F hw τ hc R) := by
  have hraw := (sourceRestart_raw_process_progressive B hm hc τ hτ R.process R.progressive).adapted
  intro t
  have hle : hτ.measurableSpace ≤ shiftedStoppingFiltration hτ t :=
    IsStoppingTime.measurableSpace_mono hτ (stopping_time_add_nnreal hτ t)
      (fun ω => WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show 0 ≤ t from zero_le)))
  have hprod : hτ.measurableSpace.prod (inferInstance : MeasurableSpace upperHalfPlane) ≤
      (shiftedStoppingFiltration hτ t).prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hle) le_rfl
  exact @weightedImageMass_measurable Ω upperHalfPlane (shiftedStoppingFiltration hτ t) inferInstance
    (fun ω => R.process t (sourceRestartDriverPath B hc τ ω)) (hraw t)
    (fun ω => (R.radon t _).2)
    (fun p => stoppedMassPoint B κ γ G F hw τ p.1 p.2)
    ((stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ).mono hprod le_rfl)
    (fun p => stoppedMassWeight B κ F τ p.1 p.2)
    ((stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ).mono hprod le_rfl)

include hm hτ in
theorem stoppedFreshMass_paths
    {P : Measure Ω} (hκ : 0 < κ)
    (hpaths : ∀ᵐ ω ∂P,
      R.process 0 (sourceRestartDriverPath B hc τ ω)=0 ∧
      Monotone (fun t => R.process t (sourceRestartDriverPath B hc τ ω)) ∧
      (∀ f : C_c(upperHalfPlane,ℝ), Continuous
        (fun t => ∫ z, f z ∂(R.process t (sourceRestartDriverPath B hc τ ω)))) ∧
      ∀ t, R.process t (sourceRestartDriverPath B hc τ ω) ≤
        R.terminal (sourceRestartDriverPath B hc τ ω))
    (hfin : ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω)) :
    ∀ᵐ ω ∂P, PositiveMassPaths
      (fun t => stoppedFreshMass B κ γ G F hw τ hc R t ω)
      (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω) := by
  have hJ := stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ
  have hW := stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ
  filter_upwards [hpaths,hfin] with ω hp hf
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
  change PositiveMassPaths (fun t => weightedImageMass J w (N t)) (weightedImageMass J w ν)
  exact @weightedImageMass_positive_paths N ν
    (R.terminal_radon (sourceRestartDriverPath B hc τ ω)).1
    hp.1 hp.2.1 hp.2.2.2 hp.2.2.1 J hJm w hwm hf

include hm hτ in
theorem stoppedFreshMass_positive_test_adapted (hκ : 0 < κ)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    Adapted (shiftedStoppingFiltration hτ)
      (fun t ω => ∫ z, f z ∂(stoppedFreshMass B κ γ G F hw τ hc R t ω)) := by
  intro t
  exact @positive_test_integral_measurable Ω (shiftedStoppingFiltration hτ t) _
    (stoppedFreshMass_adapted B κ γ G F hw τ hc R hm hτ hκ t) f hf

end Multipoint
end SLEExactGauge

end

end OAI
