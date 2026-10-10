import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleShellEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The exact flux identity extends across the regular origin. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

private theorem transformed_flux (A S u v : ℂ) :
    (star (A*u)*(A*(v+S*u))).im =
      ‖A‖^2*((star u*v).im+S.im*‖u‖^2) := by
  rw [Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem spectralLiouville_flux_formula (h r : ℝ) (hr : 0 < r) (u v : ℂ) :
    spectralScalarFlux
      (homogeneousSpectralLocalizationFactor h r*u,
        homogeneousSpectralLocalizationFactor h r*(v+homogeneousSpectralLocalizationSlope h r*u)) =
      r^11*(star u*v).im+h*r^12/4*‖u‖^2 := by
  have hS : (homogeneousSpectralLocalizationSlope h r).im = h*r/4 := by
    have hc : (11/(2*(r : ℂ)) : ℂ) = ((11/(2*r) : ℝ) : ℂ) := by push_cast; rfl
    rw [homogeneousSpectralLocalizationSlope,hc]
    norm_num [Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.div_im]
  rw [spectralScalarFlux,transformed_flux,spectralLiouvilleFactor_norm_sq h r hr,hS]
  ring

noncomputable def spectralPhysicalFlux (f g : ℝ → ℂ) (r : ℝ) : ℝ :=
  r^11*((star (f r)*deriv f r).im+(star (g r)*deriv g r).im)+
    r^12/4*(‖f r‖^2-‖g r‖^2)

theorem spectralPhysicalFlux_eq (f g : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    spectralPhysicalFlux f g r =
      spectralScalarFlux (spectralPhysicalLiouvillePair f g r).1+
        spectralScalarFlux (spectralPhysicalLiouvillePair f g r).2 := by
  dsimp only [spectralPhysicalLiouvillePair,homogeneousSpectralLocalizationState]
  rw [spectralLiouville_flux_formula 1 r hr,spectralLiouville_flux_formula (-1) r hr]
  dsimp only [spectralPhysicalFlux]
  ring

theorem spectralPhysicalFlux_continuous (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) : Continuous (spectralPhysicalFlux f g) := by
  have hdf := hf.continuous_deriv (by norm_num)
  have hdg := hg.continuous_deriv (by norm_num)
  unfold spectralPhysicalFlux
  fun_prop

theorem spectralPhysicalFlux_hasDerivAt
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (spectralPhysicalFlux f g)
      ((a+lam.re-3)*(r^11*(‖g r‖^2-‖f r‖^2))) r := by
  have hd := spectralPhysicalLiouvillePair_flux_hasDerivAt a b eta m Q lam f g hf hg he r hr
  have heq : spectralPhysicalFlux f g =ᶠ[𝓝 r]
      (fun t => spectralScalarFlux (spectralPhysicalLiouvillePair f g t).1+
        spectralScalarFlux (spectralPhysicalLiouvillePair f g t).2) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact spectralPhysicalFlux_eq f g t ht
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  simp only [← Complex.sq_norm,spectralPhysicalLiouvillePair,homogeneousSpectralLocalizationState,
    norm_mul,mul_pow,spectralLiouvilleFactor_norm_sq 1 r hr,spectralLiouvilleFactor_norm_sq (-1) r hr]
  ring

theorem spectralPhysicalLiouvillePair_flux_integral
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (R : ℝ) (hR : 0 < R) :
    spectralScalarFlux (spectralPhysicalLiouvillePair f g R).1+
      spectralScalarFlux (spectralPhysicalLiouvillePair f g R).2 =
      (a+lam.re-3)*(∫ r in (0 : ℝ)..R, r^11*(‖g r‖^2-‖f r‖^2)) := by
  have hs : Continuous (fun r : ℝ => (a+lam.re-3)*(r^11*(‖g r‖^2-‖f r‖^2))) := by
    have hfc := hf.continuous
    have hgc := hg.continuous
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
    (spectralPhysicalFlux_continuous f g hf hg).continuousOn
    (fun r hr => spectralPhysicalFlux_hasDerivAt a b eta m Q lam f g hf hg he r hr.1)
    (hs.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_const_mul] at hi
  rw [← spectralPhysicalFlux_eq f g R hR]
  simpa only [spectralPhysicalFlux,zero_pow (by norm_num : 11 ≠ 0),zero_pow (by norm_num : 12 ≠ 0),
    zero_mul,zero_div,add_zero,sub_zero] using hi.symm

end DefocusingNLS

end OAI
