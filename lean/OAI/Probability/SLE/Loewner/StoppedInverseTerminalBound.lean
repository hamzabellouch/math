import OAI.Probability.SLE.Loewner.StoppedInverseGreenMean
import OAI.Probability.SLE.Mass.GreenMeasureSupport

namespace OAI

/-! The transported fresh terminal mass is locally integrable. The bound
comes from the original canonical Green kernel at the stopping time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma halfPlaneStoppingGreenMeasure_finite_time
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (τ : Ω → ℝ≥0) (ω : Ω) :
    halfPlaneStoppingGreenMeasure κ B γ G (fun ω => (τ ω:ℝ≥0∞)) ω =
      halfPlaneGreenMeasure κ B γ G (τ ω) ω := by
  simp only [halfPlaneStoppingGreenMeasure,halfPlaneGreenMeasure,stoppingGreen,
    ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]

theorem CanonicalMass.green_at_finite_stop_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0))) :
    P.bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω) ω) ≤ initialGreenMeasure κ := by
  have hk := C.kernel (fun ω => (τ ω:WithTop ℝ≥0)) hτ univ MeasurableSet.univ
  simp only [Measure.restrict_univ,C.rational.mean] at hk
  rw [hk]
  apply Measure.le_iff.mpr
  intro A _
  simp only [Measure.add_apply]
  exact le_add_left le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun t =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))

include C hB hc hκ F hw τ hτ R he hpublished in
theorem CanonicalMass.stoppedFreshTerminalMass_mean_le :
    P.bind (stoppedFreshTerminalMass B κ γ G F hw τ hc R) ≤ initialGreenMeasure κ := by
  have hk := C.stoppedFreshTerminalMass_published_kernel hB hc hκ F hw τ hτ R he
    hpublished univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hk
  rw [hk]
  exact C.green_at_finite_stop_mean_le τ hτ

include C hB hc hκ F hw τ hτ R he hpublished in
theorem CanonicalMass.stoppedFreshTerminalMass_ae_finite_on_compacts :
    ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (stoppedFreshTerminalMass B κ γ G F hw τ hc R ω) := by
  let D := localTestFamily upperHalfPlane
  let M := stoppedFreshTerminalMass B κ γ G F hw τ hc R
  have hM : Measurable M := stoppedFreshTerminalMass_measurable B κ γ G F hw τ
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc hτ hκ R
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hbound := C.stoppedFreshTerminalMass_mean_le hB hc hκ F hw τ hτ R he hpublished
  have hfin (n : ℕ) : ∀ᵐ ω ∂P, M ω (D.compactSet n) < ∞ := by
    apply ae_lt_top ((Measure.measurable_coe (D.isCompact n).measurableSet).comp hM)
    change (∫⁻ ω, M ω (D.compactSet n) ∂P) ≠ ∞
    rw [← Measure.bind_apply (D.isCompact n).measurableSet hM.aemeasurable]
    exact (lt_of_le_of_lt (hbound (D.compactSet n)) (D.isCompact n).measure_lt_top).ne
  filter_upwards [ae_all_iff.mpr hfin] with ω hω
  constructor
  intro K hK
  obtain ⟨n,hn⟩ := D.exhaustive K hK
  exact lt_of_le_of_lt (measure_mono hn) (hω n)

end SLEExactGauge.Multipoint

end

end OAI
