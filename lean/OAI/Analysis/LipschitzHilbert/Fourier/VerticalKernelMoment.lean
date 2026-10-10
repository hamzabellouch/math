import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinKernel

namespace OAI

/-! The second absolute moment of a modulated bin kernel has exactly the
square of its physical width. The carrier does not affect it. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_second_absolute_moment_integrable (K : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => t^2*‖K t‖) := by
  simpa only [Real.norm_eq_abs,sq_abs] using K.integrable_pow_mul volume 2

theorem modulatedTimeKernel_moment2_pointwise (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    t^2*‖modulatedTimeKernel K W center t‖=W*((t/W)^2*‖K (t/W)‖) := by
  rw [modulatedTimeKernel_norm K W center t hW]
  field_simp

theorem modulatedTimeKernel_moment2_integrable (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Integrable (fun t => t^2*‖modulatedTimeKernel K W center t‖) := by
  have hi := ((schwartz_second_absolute_moment_integrable K).comp_mul_right' (inv_ne_zero hW.ne')).const_mul W
  apply hi.congr
  filter_upwards [] with t
  simpa only [div_eq_mul_inv] using (modulatedTimeKernel_moment2_pointwise K W center t hW).symm

theorem modulatedTimeKernel_moment2 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, t^2*‖modulatedTimeKernel K W center t‖)=W^2*(∫ t, t^2*‖K t‖) := by
  simp_rw [modulatedTimeKernel_moment2_pointwise K W center _ hW]
  rw [integral_const_mul,
    Measure.integral_comp_div (fun t => t^2*‖K t‖) W,abs_of_pos hW,smul_eq_mul]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
