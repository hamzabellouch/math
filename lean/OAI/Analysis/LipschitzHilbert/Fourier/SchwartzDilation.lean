import OAI.Analysis.LipschitzHilbert.Packets.ScaledPlanarPacket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! Exact horizontal dilation for Schwartz packets, including the Fourier
and measure factors needed to normalize different top lengths. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert

def schwartzDilation (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => r*x) (by fun_prop)
    (show AntilipschitzWith ‖r⁻¹‖₊ (fun x : ℝ => r*x) by
      simpa only [sub_zero,div_eq_mul_inv,inv_inv,mul_comm] using
        affineRescale_antilipschitz 0 r⁻¹ (inv_ne_zero hr)) f

@[simp] theorem schwartzDilation_apply (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) (x : ℝ) :
    schwartzDilation f r hr x = f (r*x) := rfl

theorem schwartzDilation_deriv (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) (x : ℝ) :
    deriv (schwartzDilation f r hr) x = (r:ℂ)*deriv f (r*x) := by
  have h := (f.hasDerivAt (r*x)).scomp x ((hasDerivAt_id x).const_mul r)
  simpa only [schwartzDilation,SchwartzMap.compCLMOfAntilipschitz_apply,Function.comp_apply,
    id_eq,mul_one,Complex.real_smul] using h.deriv

theorem schwartzDilation_fourier (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) (ξ : ℝ) :
    𝓕 (schwartzDilation f r hr) ξ = |r⁻¹| • 𝓕 f (ξ/r) := by
  simp only [SchwartzMap.fourier_coe,Real.fourier_real_eq,schwartzDilation_apply]
  have hphase (x : ℝ) : -(r*x*(ξ/r)) = -(x*ξ) := by field_simp
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => Real.fourierChar (-(x*(ξ/r))) • f x) r
  simpa only [hphase] using h

theorem schwartzDilation_energy (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) :
    (∫ x, ‖schwartzDilation f r hr x‖^2) = |r⁻¹| * (∫ x, ‖f x‖^2) := by
  simpa only [schwartzDilation_apply,smul_eq_mul] using
    Measure.integral_comp_mul_left (fun x : ℝ => ‖f x‖^2) r

theorem lintegral_dilation (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (r : ℝ) (hr : r ≠ 0) :
    (∫⁻ x, g (r*x)) = ENNReal.ofReal |r⁻¹| * (∫⁻ x, g x) := by
  rw [← lintegral_map hg (show Measurable (fun x : ℝ => r*x) by fun_prop)]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,lintegral_smul_measure,smul_eq_mul]

theorem schwartzDilation_low (f : SchwartzMap ℝ ℂ) (r a : ℝ) (hr : 0 < r)
    (h : ∀ ξ, |ξ| < a/r → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : |ξ| < a) :
    𝓕 (schwartzDilation f r hr.ne') ξ = 0 := by
  rw [schwartzDilation_fourier,h (ξ/r),smul_zero]
  rw [abs_div,abs_of_pos hr]
  exact (div_lt_div_iff_of_pos_right hr).mpr hξ

theorem schwartzDilation_high (f : SchwartzMap ℝ ℂ) (r b : ℝ) (hr : 0 < r)
    (h : ∀ ξ, b/r < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : b < |ξ|) :
    𝓕 (schwartzDilation f r hr.ne') ξ = 0 := by
  rw [schwartzDilation_fourier,h (ξ/r),smul_zero]
  rw [abs_div,abs_of_pos hr]
  exact (div_lt_div_iff_of_pos_right hr).mpr hξ

end LipschitzHilbert

end

end OAI
