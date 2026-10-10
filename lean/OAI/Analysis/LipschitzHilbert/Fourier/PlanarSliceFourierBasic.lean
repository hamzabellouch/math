import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzDecay
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! Product-Lebesgue Fourier transforms and transverse partial transforms
of general planar Schwartz functions. The phase is `exp(-2πi(xξ+yη))`. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def planarFourier (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) : ℂ :=
  ∫ z, Real.fourierChar (-(z.1 * frequency.1 + z.2 * frequency.2)) • f z
    ∂volume.prod volume

def planarSliceFourier (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω b : ℝ) : ℂ :=
  𝓕 (planarSchwartzSlice f b s) ω

theorem planarSliceFourier_eq (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω b : ℝ) :
    planarSliceFourier f s ω b =
      ∫ x, Real.fourierChar (-(x * ω)) • f (x, b + s * x) := by
  simp only [planarSliceFourier, SchwartzMap.fourier_coe, Real.fourier_eq,
    Real.inner_apply, planarSchwartzSlice_apply]

theorem planar_shear_integrable (f : SchwartzMap (ℝ × ℝ) ℂ) (s : ℝ) :
    Integrable (fun z : ℝ × ℝ => f (z.1, z.2 + s * z.1)) (volume.prod volume) := by
  exact (slopeShear_measurePreserving s).integrable_comp_of_integrable f.integrable

theorem planar_slice_integrand_integrable (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.fourierChar (-(z.1 * ω)) •
      f (z.1, z.2 + s * z.1)) (volume.prod volume) := by
  apply (planar_shear_integrable f s).norm.mono'
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Circle.norm_smul]
    exact le_rfl

theorem planarSliceFourier_integrable (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω : ℝ) :
    Integrable (planarSliceFourier f s ω) := by
  have h := (planar_slice_integrand_integrable f s ω).integral_prod_right
  rw [funext (planarSliceFourier_eq f s ω)]
  exact h

theorem planar_slice_uniform_bound (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω b x : ℝ) :
    ‖Real.fourierChar (-(x * ω)) • f (x, b + s * x)‖ ≤
      planarEnvelopeConstant f 1 * lineEnvelope 0 1 1 x := by
  rw [Circle.norm_smul]
  apply (planar_schwartz_envelope f 1 (x, b + s * x)).trans
  have hline : lineEnvelope 0 1 1 (b + s * x) ≤ 1 := by
    simpa only [lineEnvelope, pow_zero, inv_one] using
      (lineEnvelope_antitone 0 1 (b + s * x) (show 0 ≤ 1 by omega))
  calc
    _ = (planarEnvelopeConstant f 1 * lineEnvelope 0 1 1 x) *
        lineEnvelope 0 1 1 (b + s * x) := by ring
    _ ≤ _ := mul_le_of_le_one_right
      (mul_nonneg (planarEnvelopeConstant_pos f 1).le (lineEnvelope_nonneg 0 1 1 x)) hline

theorem planarSliceFourier_continuous (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω : ℝ) :
    Continuous (planarSliceFourier f s ω) := by
  simp only [funext (planarSliceFourier_eq f s ω)]
  apply continuous_of_dominated
    (bound := fun x => planarEnvelopeConstant f 1 * lineEnvelope 0 1 1 x)
  · intro b
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro b
    exact Filter.Eventually.of_forall (planar_slice_uniform_bound f s ω b)
  · exact (integrable_lineEnvelope_one 0 1 (by norm_num)).const_mul _
  · exact Filter.Eventually.of_forall (fun x =>
      continuous_const.smul (f.continuous.comp (by fun_prop)))

end LipschitzHilbert

end

end OAI
