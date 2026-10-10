import OAI.Probability.SLE.Geometry.RestartFutureGreen
import OAI.Probability.SLE.Geometry.CanonicalGreenPast
import OAI.Probability.SLE.Mass.StoppedInverseMass

namespace OAI

/-! Every later Green remainder transforms under the same stopped inverse
map and the same derivative weight as the canonical mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance stoppedFutureGreenDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance stoppedFutureGreenDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

 theorem stopped_future_green_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0))) (hκ : 0 < κ)
    (hFresh : ∀ᵐ ω ∂P, ∃ (β : ℝ≥0 → ℂ) (G' F' : ℝ≥0 → ℂ → ℂ),
      IsCapacityTwoWitness (fun t => Real.sqrt κ*B (τ ω+t) ω-Real.sqrt κ*B (τ ω) ω) β G' F') :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω) (stoppedMassWeight B κ F τ ω)
        (canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)) =
      halfPlaneGreenMeasure κ B γ G (τ ω+t) ω := by
  have hJ := stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ
  have hW := stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ
  filter_upwards [hFresh] with ω hω
  obtain ⟨β,G',F',hb⟩ := hω
  have hb' : IsCapacityTwoWitness
      (fun s => Real.sqrt κ*(sourceRestartDriverPath B hc τ ω) s) β G' F' := by
    convert hb using 1
    funext s
    change Real.sqrt κ*(B (τ ω+s) ω-B (τ ω) ω) = _
    ring
  have hpair : @Measurable upperHalfPlane (Ω × upperHalfPlane) inferInstance
      (hτ.measurableSpace.prod inferInstance) (fun z => (ω,z)) :=
    @measurable_prodMk_left Ω upperHalfPlane hτ.measurableSpace inferInstance ω
  have hJω : Measurable (stoppedMassPoint B κ γ G F hw τ ω) :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) upperHalfPlane
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassPoint B κ γ G F hw τ p.1 p.2) (fun z => (ω,z)) hJ hpair
  have hWω : Measurable (stoppedMassWeight B κ F τ ω) :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) ℝ≥0∞
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassWeight B κ F τ p.1 p.2) (fun z => (ω,z)) hW hpair
  intro t
  rw [canonicalGreenMass_eq κ _ hb' t]
  have hdriver : (fun s => Real.sqrt κ*(sourceRestartDriverPath B hc τ ω) s) =
      (fun s => Real.sqrt κ*B (τ ω+s) ω-Real.sqrt κ*B (τ ω) ω) := by
    funext s
    change Real.sqrt κ*(B (τ ω+s) ω-B (τ ω) ω) = _
    ring
  rw [hdriver]
  apply Measure.ext
  intro A hA
  let f : upperHalfPlane → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have htest := restart_future_halfPlane_green_test (hw ω) ((hc ω).const_mul _)
    (τ ω) hb hκ t f
  calc
    _ = ∫⁻ z, f z ∂weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω)
        (stoppedMassWeight B κ F τ ω)
        ((volume.withDensity (fun z => ENNReal.ofReal
          (greenDensity κ (fun s => Real.sqrt κ*B (τ ω+s) ω-Real.sqrt κ*B (τ ω) ω)
            β G' t z))).comap Subtype.val) := by
      rw [lintegral_indicator hA,lintegral_one,Measure.restrict_apply_univ]
    _ = _ := (weightedImageMass_lintegral _ hJω _ hWω _ f hf).trans htest
    _ = halfPlaneGreenMeasure κ B γ G (τ ω+t) ω A := by
      rw [lintegral_indicator hA,lintegral_one,Measure.restrict_apply_univ]
      rfl

end SLEExactGauge.Multipoint

end

end OAI
