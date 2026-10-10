import OAI.Probability.SLE.Mass.CanonicalMassConstruction
import OAI.Probability.SLE.Mass.RawMassFunctional

namespace OAI

/-! The canonical finite-time mass admits one raw nonanticipating functional
on continuous real driver paths. No future-dependent modification is used. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal CompactlySupported

namespace SLEExactGauge.Multipoint

local instance canonicalRawDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance canonicalRawDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.exists_raw_nonanticipating_functional
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    ∃ R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane,
      IsProgressive driverPathFiltration R ∧
      (∀ t p, (R t p).Regular ∧ IsFiniteMeasureOnCompacts (R t p)) ∧
      (∀ t p q, (∀ s ≤ t, p s=q s) → R t p=R t q) ∧
      ∀ᵐ ω ∂P, ∀ t, R t (sourceDriverPath B hBc ω) = C.process t ω := by
  apply exists_raw_progressive_radon_factor P B
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hBc C.process
    C.progressive.adapted (fun t ω => (C.radon t ω).1)
  filter_upwards [C.paths] with ω hω
  exact hω.continuous_tests

end SLEExactGauge.Multipoint

end

end OAI
