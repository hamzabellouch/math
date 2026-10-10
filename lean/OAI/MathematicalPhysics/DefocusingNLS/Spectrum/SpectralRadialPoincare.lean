import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialHardyBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexScalarAction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexWeightedSquare

namespace OAI

/-! A fixed-ball radial Poincare estimate with its boundary trace follows
from the Hardy identity at constant weight. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralComplex_radialHardy (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    16*(∫ r in (0 : ℝ)..R, r^9*‖f r‖^2) ≤
      (∫ r in (0 : ℝ)..R, r^11*‖deriv f r‖^2)+4*R^10*‖f R‖^2 := by
  have hfr : ContDiff ℝ 1 (fun r => (f r).re) := Complex.reCLM.contDiff.comp hf
  have hfi : ContDiff ℝ 1 (fun r => (f r).im) := Complex.imCLM.contDiff.comp hf
  have hr := radialHardyInequality_boundary 0 R le_rfl (by norm_num) hR _ hfr
  have hi := radialHardyInequality_boundary 0 R le_rfl (by norm_num) hR _ hfi
  simp only [radialHardyWeight,radialHardyFlux,mul_zero,Real.rpow_zero,mul_one,
    radialComplex_deriv_re f (hf.differentiable (by norm_num))] at hr
  simp only [radialHardyWeight,radialHardyFlux,mul_zero,Real.rpow_zero,mul_one,
    radialComplex_deriv_im f (hf.differentiable (by norm_num))] at hi
  have hv := spectralComplex_integral_sq R (fun r => r^9) f (continuous_id.pow 9) hf.continuous
  have hd := spectralComplex_integral_sq R (fun r => r^11) (deriv f) (continuous_id.pow 11) hf.continuous_deriv_one
  have he : 4*R^10*((f R).re^2+(f R).im^2)=4*R^10*‖f R‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply]
    ring
  nlinarith only [hr,hi,hv,hd,he]

theorem spectralRadial_weightedPoincare (R c M : ℝ) (hR : 0 ≤ R) (hc : 0 < c) (hM : 0 ≤ M)
    (mu : ℝ → ℝ) (hmu : Continuous mu)
    (hbounds : ∀ r ∈ Icc 0 R, c ≤ mu r ∧ mu r ≤ M) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    16*c*(∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2) ≤
      M*R^2*(∫ r in (0 : ℝ)..R, r^11*mu r*‖deriv f r‖^2)+4*c*M*R^12*‖f R‖^2 := by
  have hfd := hf.continuous_deriv_one
  have hfc := hf.continuous
  have h9 : Continuous (fun r : ℝ => r^9*‖f r‖^2) := by fun_prop
  have h11 : Continuous (fun r : ℝ => r^11*‖deriv f r‖^2) := by fun_prop
  have hval : Continuous (fun r : ℝ => r^11*mu r*‖f r‖^2) := by fun_prop
  have hder : Continuous (fun r : ℝ => r^11*mu r*‖deriv f r‖^2) := by fun_prop
  have hupper : (∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2) ≤
      M*R^2*(∫ r in (0 : ℝ)..R, r^9*‖f r‖^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR (hval.intervalIntegrable 0 R)
      ((h9.const_mul (M*R^2)).intervalIntegrable 0 R)
    intro r hr
    have hpower : r^2 ≤ R^2 := pow_le_pow_left₀ hr.1 hr.2 2
    have hbase := mul_le_mul (hbounds r hr).2 hpower (sq_nonneg r) hM
    have hh := mul_le_mul_of_nonneg_right hbase (mul_nonneg (pow_nonneg hr.1 9) (sq_nonneg ‖f r‖))
    nlinarith only [hh]
  have hlower : c*(∫ r in (0 : ℝ)..R, r^11*‖deriv f r‖^2) ≤
      (∫ r in (0 : ℝ)..R, r^11*mu r*‖deriv f r‖^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR ((h11.const_mul c).intervalIntegrable 0 R) (hder.intervalIntegrable 0 R)
    intro r hr
    have hh := mul_le_mul_of_nonneg_right (hbounds r hr).1
      (mul_nonneg (pow_nonneg hr.1 11) (sq_nonneg ‖deriv f r‖))
    nlinarith only [hh]
  have hH := spectralComplex_radialHardy R hR f hf
  have h1 := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 16*c)
  have h2 := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ c*M*R^2)
  have h3 := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ M*R^2)
  nlinarith only [h1,h2,h3]

end DefocusingNLS

end OAI
