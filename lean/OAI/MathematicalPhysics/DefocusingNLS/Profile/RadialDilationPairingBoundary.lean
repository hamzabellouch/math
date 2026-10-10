import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexDilationIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDilationDecomposition
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalContinuousTest

namespace OAI

/-! The dilation cross pairing is a real volume term plus its exact complex
boundary correction. Its imaginary part is entirely a boundary flux. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_dilation_pairing_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    radialComplexDilationPairing n z R ((6-2*radialShootingA n)/2) f g =
      ((2*(∫ r in (0 : ℝ)..R, radialMassFlux n z r*(star (deriv g r)*f r).re+
        ((6-2*radialShootingA n)/2)*radialMassDensity n z r*(star (g r)*f r).re) : ℝ) : ℂ)-
      (radialMassFlux n z R : ℂ)*star (f R)*g R := by
  let c := 6-2*radialShootingA n
  let s := c/2
  let F := fun r : ℝ => (radialMassFlux n z r : ℂ)*star (f r)*g r
  let H := fun r : ℝ => (c*radialMassDensity n z r : ℝ)*star (f r)*g r+
    (radialMassFlux n z r : ℂ)*(star (deriv f r)*g r+star (f r)*deriv g r)
  let V := fun r : ℝ => radialMassFlux n z r*(star (deriv g r)*f r).re+
    s*radialMassDensity n z r*(star (g r)*f r).re
  let I := fun r : ℝ => (radialMassDensity n z r : ℂ)*
    spectralDilationCross (radialMatchedVelocity n z r) s (f r) (g r) (deriv f r) (deriv g r)
  have hmc := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hwc := radialMatchedVelocity_continuousOn n z hX hz R
  have hvc := radialMassFlux_continuousOn n z hX hz R
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdf := hf.continuous_deriv_one
  have hdg := hg.continuous_deriv_one
  have hFc : ContinuousOn F (Icc 0 R) := by dsimp only [F]; fun_prop
  have hHc : ContinuousOn H (Icc 0 R) := by dsimp only [H]; fun_prop
  have hVc : ContinuousOn V (Icc 0 R) := by dsimp only [V]; fun_prop
  have hIc : ContinuousOn I (Icc 0 R) := by dsimp only [I,spectralDilationCross]; fun_prop
  have hd r (hr : r ∈ Ioo 0 R) : HasDerivAt F (H r) r := by
    have hh := (((radialMassFlux_hasDerivAt n z hX hz r hr.1).ofReal_comp.mul
      (hf.differentiable (by norm_num) r).hasDerivAt.star).mul
      (hg.differentiable (by norm_num) r).hasDerivAt)
    apply hh.congr_deriv
    dsimp only [H,c,Pi.mul_apply]
    push_cast
    ring
  have ht := spectralClassicalFlux_continuous_test R hR F H (fun _ => 1) hFc hHc hd
    (by simp [F,radialMassFlux,radialMassDensity]) contDiff_const
  simp only [deriv_const,star_one,star_zero,zero_mul,one_mul,intervalIntegral.integral_zero,zero_add] at ht
  have hpoint r : I r = ((2*V r : ℝ) : ℂ)-H r := by
    have hh := congrArg (fun x : ℂ => (radialMassDensity n z r : ℂ)*x)
      (spectralDilationCross_decomposition (radialMatchedVelocity n z r) s
        (f r) (g r) (deriv f r) (deriv g r))
    dsimp only [I,V,H,radialMassFlux,radialMatchedVelocity] at hh ⊢
    dsimp only [s,c] at hh ⊢
    push_cast at hh ⊢
    linear_combination hh
  change (∫ r in (0 : ℝ)..R, I r) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_sub]
  · rw [ht,intervalIntegral.integral_ofReal,intervalIntegral.integral_const_mul]
  · exact (Complex.continuous_ofReal.comp_continuousOn (hVc.const_mul 2)).intervalIntegrable_of_Icc hR
  · exact hHc.intervalIntegrable_of_Icc hR

theorem radialMatched_dilation_pairing_im (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (radialComplexDilationPairing n z R ((6-2*radialShootingA n)/2) f g).im =
      radialMassFlux n z R*(star (g R)*f R).im := by
  rw [radialMatched_dilation_pairing_boundary n z hX hz R hR f g hf hg]
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

end DefocusingNLS

end OAI
