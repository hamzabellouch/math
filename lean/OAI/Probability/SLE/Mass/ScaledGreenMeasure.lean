import OAI.Probability.SLE.Mass.DilationMass
import OAI.Probability.SLE.Loewner.RawScaledGreenKernel
import OAI.Probability.SLE.Geometry.ScaledMarkedKernel

namespace OAI

/-! Killed Green measures scale by the same dimension-weighted spatial
pushforward as the canonical mass, including points no longer surviving. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance scaledGreenMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance scaledGreenBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma halfPlaneGreenMeasure_scaled {Ω : Type*} (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (c : ℝ≥0) (hc : 0 < c) (t : ℝ≥0) (ω : Ω) :
    halfPlaneGreenMeasure κ (scaledBrownianDriver c B)
      (fun ω => sourceScaleTrace c (γ ω)) (fun ω => sourceScaleChart c (G ω)) (c^2*t) ω=
      dilationMass κ c hc (halfPlaneGreenMeasure κ B γ G t ω) := by
  unfold halfPlaneGreenMeasure
  apply dilationMass_realDensity
  intro z _hz
  have h := source_scale_greenDensity κ c hc (fun t => Real.sqrt κ*B t ω)
    (γ ω) (G ω) (F ω) (hw ω) (c^2*t) z
  rw [source_scale_time_mul_sq c t hc] at h
  simpa only [scaledBrownianDriver,mul_left_comm (Real.sqrt κ) (c:ℝ)] using h

lemma canonicalGreenMass_scaled {Ω : Type*} (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (c : ℝ≥0) (hcp : 0 < c) (t : ℝ≥0) (ω : Ω) :
    canonicalGreenMass κ (c^2*t)
      (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc) ω)=
      dilationMass κ c hcp (halfPlaneGreenMeasure κ B γ G t ω) := by
  have hwc : IsCapacityTwoWitness (fun t => Real.sqrt κ*scaledBrownianDriver c B t ω)
      (sourceScaleTrace c (γ ω)) (sourceScaleChart c (G ω)) (sourceScaleChart c (F ω)) := by
    have h := source_scale_witness c hcp (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) (F ω) (hw ω)
    simpa only [scaledBrownianDriver,mul_left_comm (Real.sqrt κ) (c:ℝ)] using h
  have he := canonicalGreenMass_eq κ
    (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc) ω)
    hwc (c^2*t)
  change canonicalGreenMass κ (c^2*t)
    (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc) ω)=
      halfPlaneGreenMeasure κ (scaledBrownianDriver c B)
        (fun ω => sourceScaleTrace c (γ ω)) (fun ω => sourceScaleChart c (G ω)) (c^2*t) ω at he
  rw [he]
  exact halfPlaneGreenMeasure_scaled κ B γ G F hw c hcp t ω

end SLEExactGauge.Multipoint

end

end OAI
