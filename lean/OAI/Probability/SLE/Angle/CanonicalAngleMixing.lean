import OAI.Probability.SLE.Angle.ActualAngleSpectral

namespace OAI

/-! Uniform finite-centered mixing for the actual canonical angle kernel.
The constants are derived from the positive spectral law, not assumed. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance angleMixingMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance angleMixingBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma angleSpectralLaw_lintegral_bounds {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤ (∫⁻ φ, f φ ∂angleSpectralLaw κ u θ) ∧
    (∫⁻ φ, f φ ∂angleSpectralLaw κ u θ) ≤ 2*(∫⁻ φ, f φ ∂Target.angleLaw κ) := by
  rw [angleSpectralLaw,lintegral_withDensity_eq_lintegral_mul _
    (angleSpectralKernel_measurable hκ hu θ).ennreal_ofReal hf]
  have hb (φ : ℝ) : (1/2:ℝ≥0∞)≤ENNReal.ofReal (angleSpectralKernel κ u θ φ) ∧
      ENNReal.ofReal (angleSpectralKernel κ u θ φ)≤2 := by
    have h := angleSpectralKernel_bounds hκ hu θ φ
    constructor
    · simpa using ENNReal.ofReal_le_ofReal h.1
    · simpa using ENNReal.ofReal_le_ofReal h.2
  constructor
  · calc
      _ = (1/2:ℝ≥0∞)*(∫⁻ φ, f φ ∂Target.angleLaw κ) := by
        rw [div_eq_mul_inv,one_div,mul_comm]
      _ = ∫⁻ φ, (1/2:ℝ≥0∞)*f φ ∂Target.angleLaw κ := (lintegral_const_mul _ hf).symm
      _ ≤ _ := lintegral_mono fun φ => mul_le_mul' (hb φ).1 le_rfl
  · calc
      _ ≤ ∫⁻ φ, (2:ℝ≥0∞)*f φ ∂Target.angleLaw κ :=
        lintegral_mono fun φ => mul_le_mul' (hb φ).2 le_rfl
      _ = _ := lintegral_const_mul _ hf

lemma Target.diskMapInv_zero_arg (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) :
    (Target.diskMapInv θ 0).arg=θ := by
  simp only [Target.diskMapInv,zero_mul,sub_zero,div_one]
  rw [Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos,hθ.1,hθ.2]

lemma canonicalAngleAverage_uniform_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : angleSpectralMixingTime κ≤u) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) :
    (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤
      canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u f θ ∧
    canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u f θ ≤
      2*(∫⁻ φ, f φ ∂Target.angleLaw κ) := by
  have hu0 : 0≤u := (angleSpectralMixingTime_pos hκ).le.trans hu
  let z := Target.diskMapInv θ 0
  have hz : z∈upperHalfPlane := Target.diskMapInv_maps hθ (by simp)
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let S : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hS := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu0
  let a := extendedMarkedAngle κ B γ G S z
  have ham : Measurable a :=
    (extendedMarkedAngle_measurable B hm hc κ γ G F hw S hS z).mono hS.measurableSpace_le le_rfl
  have he : canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ u f θ=
      ∫⁻ φ, f φ ∂angleSpectralLaw κ u θ := by
    rw [canonicalAngleAverage_eq_finiteCentered hB hBm hc hκ hκ8 γ G F hw u hu0 θ hθ f hf]
    change (∫⁻ ω, f (a ω) ∂finiteCenteredLaw P κ B γ G z u)=_
    rw [← lintegral_map' hf.aemeasurable ham.aemeasurable,
      actual_angle_law_eq_spectral hB hBm hc h0 hκ hκ8 γ G F hw z hz u hu]
    rw [Target.diskMapInv_zero_arg θ hθ]
  rw [he]
  exact angleSpectralLaw_lintegral_bounds hκ hu θ f hf

end SLEExactGauge

end

end OAI
