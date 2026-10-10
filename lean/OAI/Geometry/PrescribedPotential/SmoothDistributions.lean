import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevEmbedding

namespace OAI

/-! Smooth Distributions. -/

section

 
noncomputable section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma temperate_fderiv {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right (by simp), fun n => ?_⟩
  simpa only [norm_iteratedFDeriv_fderiv] using hf.2 (n + 1)

def directionDerivative (v : E) (f : E → ℂ) : E → ℂ := fun x => fderiv ℝ f x v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma temperate_directionDerivative (v : E) {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    (directionDerivative v f).HasTemperateGrowth := by
  have hd := temperate_fderiv hf
  unfold directionDerivative
  exact (ContinuousLinearMap.apply ℝ ℂ v).hasTemperateGrowth.comp hd

lemma temperateDistribution_eq_smul_volume {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    hf.toTemperedDistribution volume = smulLeftCLM ℂ f (volume.toTemperedDistribution) := by
  ext φ
  simp only [Function.HasTemperateGrowth.toTemperedDistribution_apply,
    smulLeftCLM_apply_apply, Measure.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply hf]
  simp only [smul_eq_mul, mul_comm]

lemma temperateDistribution_sub {f g : E → ℂ} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) :
    (hf.sub hg).toTemperedDistribution volume =
      hf.toTemperedDistribution volume - hg.toTemperedDistribution volume := by
  simp only [temperateDistribution_eq_smul_volume]
  rw [smulLeftCLM_sub hf hg]
  rfl

lemma temperateDistribution_schwartz (f : 𝓢(E, ℂ)) :
    f.hasTemperateGrowth.toTemperedDistribution volume = (f : 𝓢'(E, ℂ)) := by
  ext φ
  simp

lemma temperateDistribution_bounded (f : E →ᵇ ℂ) (hf : (f : E → ℂ).HasTemperateGrowth) :
    hf.toTemperedDistribution volume = boundedDistribution f := by
  ext φ
  rw [Function.HasTemperateGrowth.toTemperedDistribution_apply volume hf φ, boundedDistribution_apply]

lemma temperate_schwartz_integrable {f : E → ℂ} (hf : f.HasTemperateGrowth)
    (φ : 𝓢(E, ℂ)) : Integrable (fun x => φ x * f x) := by
  simpa only [SchwartzMap.smulLeftCLM_apply hf, smul_eq_mul, mul_comm] using
    (SchwartzMap.smulLeftCLM ℂ f φ).integrable (μ := volume)

 

lemma temperateDistribution_derivative (v : E) {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    (temperate_directionDerivative v hf).toTemperedDistribution volume =
      ∂_{v} (hf.toTemperedDistribution volume) := by
  ext φ
  simp only [Function.HasTemperateGrowth.toTemperedDistribution_apply,
    TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  change (∫ x, φ x * directionDerivative v f x) = -(∫ x, (∂_{v} φ) x * f x)
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := v)
    (temperate_schwartz_integrable hf (∂_{v} φ))
    (temperate_schwartz_integrable (temperate_directionDerivative v hf) φ)
    (temperate_schwartz_integrable hf φ)
  · intro x _
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (SchwartzMap.hasFDerivAt φ x).hasLineDerivAt v
  · intro x _
    exact ((hf.1.differentiable (by simp)) x).hasFDerivAt.hasLineDerivAt v

lemma temperateDistribution_eq_zero_iff {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    hf.toTemperedDistribution volume = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply (hf.1.continuous.ae_eq_iff_eq volume continuous_zero).mp
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure E))
      hf.1.continuous.locallyIntegrable
    intro g hg hc
    let φ : 𝓢(E, ℂ) := (hc.comp_left (show Complex.ofReal 0 = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
    have he := congrArg (fun t : 𝓢'(E, ℂ) => t φ) h
    change (∫ x, ((g x : ℝ) : ℂ) • f x) = 0 at he
    simpa only [Complex.real_smul, smul_eq_mul] using he
  · rintro rfl
    ext φ
    simp

lemma temperateDistribution_injective {f g : E → ℂ} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth)
    (h : hf.toTemperedDistribution volume = hg.toTemperedDistribution volume) : f = g := by
  apply sub_eq_zero.mp
  apply (temperateDistribution_eq_zero_iff (hf.sub hg)).mp
  rw [temperateDistribution_sub hf hg, h, sub_self]

end SobolevChart

end
end

end OAI
