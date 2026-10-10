import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzVerticalProjection
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL2
import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourierDerivative

namespace OAI

/-! A fixed normalization of the original vertical cutoff controls its
L1, L2 and uniform sizes without changing its frequency band or strip. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalProjectionCost (p : SchwartzMap ℝ ℂ) : ℝ :=
  1+∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖

theorem verticalProjectionCost_pos (p : SchwartzMap ℝ ℂ) : 0<verticalProjectionCost p := by
  unfold verticalProjectionCost
  have h : 0≤∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖ := integral_nonneg fun _ => norm_nonneg _
  linarith

def normalizedBandProjection (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  ((verticalProjectionCost p)⁻¹ : ℂ) • schwartzVerticalProjection p w 0 f

theorem normalizedBandProjection_apply (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    normalizedBandProjection p w f z=((verticalProjectionCost p)⁻¹ : ℂ)*
      verticalConvolution (verticalProfileKernel p w 0) f z := by
  change ((verticalProjectionCost p)⁻¹ : ℂ)*schwartzVerticalProjection p w 0 f z=_
  rw [schwartzVerticalProjection_eq_convolution p w 0 hw]

theorem normalizedBandProjection_sizes (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure)≤∫ z, ‖f z‖ ∂planeMeasure ∧
      (∫ z, ‖normalizedBandProjection p w f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  let C := verticalProjectionCost p
  have hC : 0<C := verticalProjectionCost_pos p
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : C⁻¹*A≤1 := by
    rw [mul_comm,←div_eq_mul_inv]
    apply (div_le_one hC).2
    change A≤1+A
    linarith
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have hKnorm : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  have hn (z) : ‖normalizedBandProjection p w f z‖=C⁻¹*‖verticalConvolution K f z‖ := by
    rw [normalizedBandProjection_apply p w hw,norm_mul]
    simp only [C,K,norm_inv,Complex.norm_real,Real.norm_of_nonneg (verticalProjectionCost_pos p).le]
  have h1 := verticalConvolution_l1_bound K hKi hKm f f.continuous.measurable f.integrable
  have h2 := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  rw [hKnorm] at h1 h2
  constructor
  · simp_rw [hn]
    rw [integral_const_mul]
    calc
      _ ≤ C⁻¹*(A*∫ z, ‖f z‖ ∂planeMeasure) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hC.le)
      _ ≤ ∫ z, ‖f z‖ ∂planeMeasure := by
        rw [←mul_assoc]
        exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) hAC
  · simp_rw [hn,mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ (C⁻¹)^2*(A^2*∫ z, ‖f z‖^2 ∂planeMeasure) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ ∫ z, ‖f z‖^2 ∂planeMeasure := by
        rw [←mul_assoc,←mul_pow]
        exact mul_le_of_le_one_left (integral_nonneg fun _ => sq_nonneg _)
          (by nlinarith [pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hC.le) hA) hAC 2])

theorem normalizedBandProjection_uniform (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    ∀ z, ‖normalizedBandProjection p w f z‖≤1 := by
  intro z
  rw [normalizedBandProjection_apply p w hw,norm_mul]
  have hC := verticalProjectionCost_pos p
  simp only [norm_inv,Complex.norm_real,Real.norm_of_nonneg hC.le]
  have h := verticalConvolution_uniform_bound (verticalProfileKernel p w 0)
    (modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw) f 1 hf z
  rw [one_mul,show (∫ s, ‖verticalProfileKernel p w 0 s‖)=
    (∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖) from modulatedTimeKernel_l1 _ w 0 hw] at h
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hC.le)).trans
  rw [mul_comm,←div_eq_mul_inv]
  apply (div_le_one hC).2
  unfold verticalProjectionCost
  linarith

theorem normalizedBandProjection_band (p : SchwartzMap ℝ ℂ) (w c C : ℝ)
    (hp : ∀ eta, p eta≠0 → c≤eta ∧ eta≤C) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ∀ omega, planarFourier (normalizedBandProjection p w f) omega≠0 →
      c≤w*omega.2 ∧ w*omega.2≤C := by
  intro omega h
  by_contra hbad
  have hp0 : p (w*omega.2)=0 := by
    by_contra hnonzero
    exact hbad (hp _ hnonzero)
  apply h
  rw [normalizedBandProjection,planarFourier_smul,schwartzVerticalProjection_fourier]
  simp only [sub_zero,hp0,zero_mul,mul_zero]

theorem normalizedBandProjection_support (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → normalizedBandProjection p w f z=0 := by
  intro z hz
  rw [normalizedBandProjection_apply p w hw,verticalConvolution_horizontal_support _ f S hf z hz,mul_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
