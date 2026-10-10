import OAI.Probability.SLE.Loewner.CanonicalTraceCandidate

namespace OAI

/-! A measurable normalization of arbitrary continuous paths. On based
paths it is inverse to the physical-time unnormalization. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance pathNormalizationMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance pathNormalizationBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance pathNormalizationDriverPolish : PolishSpace Target.Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace

def normalizePath (κ : ℝ) (p : C(ℝ≥0,ℝ)) : Target.Driver where
  toFun t := Real.sqrt κ*(p (t/κ.toNNReal)-p 0)
  continuous_toFun := by fun_prop
  map_zero' := by simp

lemma measurable_normalizePath (κ : ℝ) : Measurable (normalizePath κ) := by
  apply ContinuousMapZero.isClosedEmbedding_toContinuousMap.measurableEmbedding.measurable_comp_iff.mp
  apply source_path_measurable
  intro t
  exact measurable_const.mul (((continuous_eval_const _).measurable).sub
    ((continuous_eval_const 0).measurable))

lemma normalize_unnormalize (κ : ℝ) (hκ : 0 < κ) (b : Target.Driver) :
    normalizePath κ (unnormalizeDriver κ b)=b := by
  ext t
  change Real.sqrt κ*(b (κ.toNNReal*(t/κ.toNNReal))/Real.sqrt κ
    -b (κ.toNNReal*0)/Real.sqrt κ)=b t
  rw [mul_div_cancel₀ _ (Real.toNNReal_pos.mpr hκ).ne']
  simp only [mul_zero,map_zero,zero_div,sub_zero]
  exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr hκ).ne'

lemma measurableEmbedding_unnormalizeDriver (κ : ℝ) (hκ : 0 < κ) :
    MeasurableEmbedding (unnormalizeDriver κ) :=
  (measurable_unnormalizeDriver κ).measurableEmbedding
    (fun b c h => by simpa only [normalize_unnormalize κ hκ] using congrArg (normalizePath κ) h)

lemma unnormalizeDriver_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    W.map (unnormalizeDriver κ)=P.map (sourceDriverPath B hc) := by
  rw [← (Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW).map_eq,
    Measure.map_map (measurable_unnormalizeDriver κ)
      (Target.normalizedDriver_measurable κ B hm hc h0)]
  congr 1
  funext ω
  exact unnormalize_normalizedDriver κ hκ B hc h0 ω

end SLEExactGauge

end

end OAI
