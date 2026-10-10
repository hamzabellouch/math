import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBernstein
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBandProjection

namespace OAI

/-! The vertical derivative of the actual band projection has L1 and
uniform bounds of order inverse bandwidth. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalDerivativeProfile (p : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (2*Real.pi*Complex.I : ℂ) • SchwartzMap.smulLeftCLM ℂ (fun s : ℝ => (s:ℂ)) p

theorem verticalDerivativeProfile_apply (p : SchwartzMap ℝ ℂ) (s : ℝ) :
    verticalDerivativeProfile p s=(2*Real.pi*Complex.I : ℂ)*(s:ℂ)*p s := by
  unfold verticalDerivativeProfile
  rw [smul_apply,SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [smul_eq_mul,mul_assoc]

theorem verticalProjection_derivative (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f)=
      (w⁻¹:ℂ) • schwartzVerticalProjection (verticalDerivativeProfile p) w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  rw [verticalSchwartzDeriv_fourier,planarFourier_smul,
    schwartzVerticalProjection_fourier,schwartzVerticalProjection_fourier,
    verticalDerivativeProfile_apply]
  simp only [sub_zero]
  push_cast
  have hwc : (w:ℂ)≠0 := by exact_mod_cast hw.ne'
  field_simp

theorem verticalProjection_derivative_sizes (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    (∫ z, ‖verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f) z‖ ∂planeMeasure)≤
      (verticalProjectionCost (verticalDerivativeProfile p)/w)*(∫ z, ‖f z‖ ∂planeMeasure) ∧
    ∀ z, ‖verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f) z‖≤
      verticalProjectionCost (verticalDerivativeProfile p)/w := by
  let q := verticalDerivativeProfile p
  let K := verticalProfileKernel q w 0
  let A := ∫ s, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) s‖
  have hA : A≤verticalProjectionCost q := by
    change A≤1+A
    linarith
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ q) w 0 hw
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ q : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hmass : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ q) w 0 hw
  have heq (z : ℝ×ℝ) : ‖verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f) z‖=
      w⁻¹*‖verticalConvolution K f z‖ := by
    rw [verticalProjection_derivative p w hw,smul_apply,norm_smul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hw.le,schwartzVerticalProjection_eq_convolution q w 0 hw]
  constructor
  · simp_rw [heq]
    rw [integral_const_mul]
    have h := verticalConvolution_l1_bound K hKi hKm f f.continuous.measurable f.integrable
    rw [hmass] at h
    calc
      _ ≤ w⁻¹*(A*∫ z, ‖f z‖ ∂planeMeasure) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hw.le)
      _ ≤ w⁻¹*(verticalProjectionCost q*∫ z, ‖f z‖ ∂planeMeasure) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA
          (integral_nonneg fun _ => norm_nonneg _)) (inv_nonneg.mpr hw.le)
      _ = _ := by dsimp [q]; ring
  · intro z
    rw [heq]
    have h := verticalConvolution_uniform_bound K hKi f 1 hf z
    rw [hmass,one_mul] at h
    calc
      _ ≤ w⁻¹*verticalProjectionCost q := mul_le_mul_of_nonneg_left (h.trans hA) (inv_nonneg.mpr hw.le)
      _ = _ := by dsimp [q]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
