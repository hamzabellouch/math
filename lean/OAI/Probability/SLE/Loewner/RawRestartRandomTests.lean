import OAI.Probability.SLE.Loewner.RawRestartGreenKernel
import OAI.Probability.SLE.Geometry.CanonicalRawMean
import OAI.Probability.SLE.Mass.ConditionalRadonRandomTests

namespace OAI

/-! The restarted Green kernel accepts arbitrary random spatial tests
measurable in the full original past at the later time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance rawRestartTestsDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawRestartTestsDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω))
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))

include C hB hc F hw R he τ hτ in
theorem CanonicalMass.raw_restarted_random_green_test
    (t : ℝ≥0) (f : Ω × upperHalfPlane → ℝ≥0∞)
    (hf : Measurable[(shiftedStoppingFiltration hτ t).prod inferInstance] f) :
    (∫⁻ ω, ∫⁻ z, f (ω,z) ∂(R.terminal (sourceRestartDriverPath B hc τ ω)) ∂P) =
      ∫⁻ ω, ∫⁻ z, f (ω,z) ∂(R.process t (sourceRestartDriverPath B hc τ ω)+
        canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)) ∂P := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hY := sourceRestartDriverPath_measurable B hm hc τ hτ
  let μ (ω : Ω) := R.terminal (sourceRestartDriverPath B hc τ ω)
  let ν (ω : Ω) := R.process t (sourceRestartDriverPath B hc τ ω)+
    canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)
  have hμ : Measurable μ := R.terminal_measurable.comp hY
  have hR : Measurable (fun ω => R.process t (sourceRestartDriverPath B hc τ ω)) :=
    (R.progressive.adapted.measurable (i := t)).comp hY
  have hG : Measurable (fun ω => canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)) :=
    (canonicalGreenMass_measurable κ t).comp hY
  have hν : Measurable ν := hR.add hG
  have hmean : P.bind μ=initialGreenMeasure κ :=
    C.restarted_raw_terminal_mean hB hc R (he.mono fun _ h => h.2) τ hτ
  have hevent (A : Set Ω) (hA : MeasurableSet[shiftedStoppingFiltration hτ t] A) :
      (P.restrict A).bind μ=(P.restrict A).bind ν := by
    have h := C.raw_restarted_green_kernel hc F hw R he hB τ hτ t A hA
    exact h.trans (bind_kernel_add _ _ _ hR hG).symm
  have htotal : P.bind μ=P.bind ν := by
    simpa only [Measure.restrict_univ] using hevent univ MeasurableSet.univ
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hμmean (K : Set upperHalfPlane) (hK : IsCompact K) : P.bind μ K < ∞ := by
    rw [hmean]
    exact hK.measure_lt_top
  have hνmean (K : Set upperHalfPlane) (hK : IsCompact K) : P.bind ν K < ∞ := by
    rw [← htotal]
    exact hμmean K hK
  exact conditional_halfPlane_random_test (shiftedStoppingFiltration hτ t)
    ((shiftedStoppingFiltration hτ).le t) P μ ν hμ hν
    (ae_of_all _ (fun ω => (R.terminal_radon _).2))
    (ae_finite_on_compacts_of_compact_mean P ν hν hνmean) hμmean hevent f hf

end SLEExactGauge.Multipoint

end

end OAI
