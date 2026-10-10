import OAI.Probability.SLE.Loewner.CanonicalCapacityWitness
import OAI.Probability.SLE.Angle.TargetPathNormalization
import OAI.Probability.SLE.Geometry.PublishedInputs

namespace OAI

/-! A capacity-two SLE presentation gives a canonical trace on its
continuous-driver law through the raw inverse-flow witness. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance traceDischargeRealMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance traceDischargeRealBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance traceDischargeComplexMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance traceDischargeComplexBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

theorem canonical_driver_trace_generation_of_witness
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)) :
    PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t) := by
  let W : Target.WienerLaw := P.map (Target.normalizedDriver κ B hc h0)
  have hW : Target.IsWiener W := Target.normalizedDriver_isWiener κ hκ B hB hm hc h0
  obtain ⟨Ψ,hΨ,hΨw⟩ := exists_canonical_capacity_witness
    κ hκ hκ8 B hB hm hc h0 γ G F hw W hW
  let Φ : C(ℝ≥0,ℝ) → C(ℝ≥0,ℂ) := Ψ ∘ normalizePath κ
  refine ⟨fun p t => Φ p t,fun t => ?_,?_⟩
  · exact (continuous_eval_const t).measurable.comp (hΨ.comp (measurable_normalizePath κ))
  · rw [← unnormalizeDriver_law κ hκ B hB hm hc h0 W hW]
    rw [ae_iff,(measurableEmbedding_unnormalizeDriver κ hκ).map_apply]
    apply ae_iff.mp
    filter_upwards [hΨw] with b hb
    have he : (fun t => Real.sqrt κ*(unnormalizeDriver κ b) t)=
        (fun t => b (κ.toNNReal*t)) := by
      funext t
      change Real.sqrt κ*(b (κ.toNNReal*t)/Real.sqrt κ)=_
      exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr hκ).ne'
    have hΦ : (Φ (unnormalizeDriver κ b) : ℝ≥0 → ℂ)=Ψ b := by
      simp only [Φ,Function.comp_apply,normalize_unnormalize κ hκ]
    rw [he,hΦ]
    exact ⟨_,_,hb⟩

end SLEExactGauge

end

end OAI
