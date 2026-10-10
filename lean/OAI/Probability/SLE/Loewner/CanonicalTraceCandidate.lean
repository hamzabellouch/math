import OAI.Probability.SLE.Loewner.TargetTraceCandidate
import OAI.Probability.SLE.Angle.TargetBrownianNormalization

namespace OAI

/-! The raw inverse-flow trace candidate has a measurable continuous-path
modification under the actual Wiener law. No trace-generation input is used. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance candidateRealMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance candidateRealBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance candidateComplexMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance candidateComplexBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

def unnormalizeDriver (κ : ℝ) (b : Target.Driver) : C(ℝ≥0,ℝ) :=
  ⟨fun t => b (κ.toNNReal*t)/Real.sqrt κ, by fun_prop⟩

lemma measurable_unnormalizeDriver (κ : ℝ) : Measurable (unnormalizeDriver κ) := by
  apply source_path_measurable
  intro t
  exact (continuous_eval_const _).measurable.div_const _

lemma unnormalize_normalizedDriver {Ω : Type*}
    (κ : ℝ) (hκ : 0 < κ) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) (ω : Ω) :
    unnormalizeDriver κ (Target.normalizedDriver κ B hc h0 ω)=sourceDriverPath B hc ω := by
  ext t
  change (Real.sqrt κ*B ((κ.toNNReal*t)/κ.toNNReal) ω)/Real.sqrt κ=B t ω
  rw [mul_div_cancel_left₀ _ (Real.toNNReal_pos.mpr hκ).ne',
    mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hκ).ne']

theorem exists_canonical_trace_candidate_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∃ Ψ : Target.Driver → C(ℝ≥0,ℂ), Measurable Ψ ∧
      (∀ ω, Ψ (Target.normalizedDriver κ B hc h0 ω)=sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      ∀ T : ℝ≥0, ∀ᵐ b ∂W,
        Tendsto (fun n => Target.rawTipApprox κ n T b) atTop (𝓝 (Ψ b T)) ∧
        Target.traceCandidate κ T b=Ψ b T := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Φ,hΦ,hΦeq,_⟩ := sourceStoppedTraceLaw κ hκ hκ8 B hB hm hc γ G F hw
  let Ψ : Target.Driver → C(ℝ≥0,ℂ) := Φ ∘ unnormalizeDriver κ
  have hΨ : Measurable Ψ := hΦ.comp (measurable_unnormalizeDriver κ)
  have hΨeq (ω : Ω) : Ψ (Target.normalizedDriver κ B hc h0 ω)=
      sourceTracePath γ (fun ω => (hw ω).1) ω := by
    change Φ (unnormalizeDriver κ (Target.normalizedDriver κ B hc h0 ω)) =
      sourceTracePath γ (fun ω => (hw ω).1) ω
    rw [unnormalize_normalizedDriver κ hκ B hc h0]
    exact hΦeq ω
  refine ⟨Ψ,hΨ,hΨeq,?_⟩
  intro T
  have hset : MeasurableSet {b : Target.Driver |
      Tendsto (fun n => Target.rawTipApprox κ n T b-Ψ b T) atTop (𝓝 (0:ℂ))} :=
    measurableSet_tendsto _ (fun n =>
      ((Target.measurable_rawTipApprox κ n).comp (measurable_const.prodMk measurable_id)).sub
        ((continuous_eval_const T).measurable.comp hΨ))
  have hLaw := Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW
  have hae : ∀ᵐ b ∂W, Tendsto (fun n => Target.rawTipApprox κ n T b-Ψ b T) atTop (𝓝 (0:ℂ)) := by
    rw [← hLaw.map_eq]
    apply (ae_map_iff hLaw.aemeasurable hset).mpr
    apply ae_of_all
    intro ω
    apply tendsto_sub_nhds_zero_iff.mpr
    have h := Target.rawTipApprox_tendsto_witness κ hκ (Target.normalizedDriver κ B hc h0 ω)
      (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω) (hw ω)
      (Target.normalizedDriver_matches κ hκ B hc h0 ω) T
    simpa only [hΨeq,sourceTracePath,ContinuousMap.coe_mk] using h
  filter_upwards [hae] with b hb
  have ht := tendsto_sub_nhds_zero_iff.mp hb
  exact ⟨ht,ht.limUnder_eq⟩

end SLEExactGauge

end

end OAI
