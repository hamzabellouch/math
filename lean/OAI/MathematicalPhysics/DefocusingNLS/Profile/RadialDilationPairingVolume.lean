import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationPairingBoundary

namespace OAI

/-! An explicit real-part formula separates the dilation pairing into two
ordinary weighted products and the already-controlled boundary term. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_dilation_pairing_re (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (radialComplexDilationPairing n z R ((6-2*radialShootingA n)/2) f g).re =
      2*((∫ r in (0 : ℝ)..R, (radialMassFlux n z r : ℂ)*star (deriv g r)*f r).re+
        ((6-2*radialShootingA n)/2)*
          (∫ r in (0 : ℝ)..R, (radialMassDensity n z r : ℂ)*star (g r)*f r).re)-
      ((radialMassFlux n z R : ℂ)*star (f R)*g R).re := by
  have hM := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hV := radialMassFlux_continuousOn n z hX hz R
  have hdf := hf.continuous_deriv_one
  have hdg := hg.continuous_deriv_one
  have hP : IntervalIntegrable (fun r => (radialMassFlux n z r : ℂ)*star (deriv g r)*f r) volume 0 R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hR
    exact ((Complex.continuous_ofReal.comp_continuousOn hV).mul hdg.star.continuousOn).mul hf.continuous.continuousOn
  have hQ : IntervalIntegrable (fun r => (radialMassDensity n z r : ℂ)*star (g r)*f r) volume 0 R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hR
    exact ((Complex.continuous_ofReal.comp_continuousOn hM).mul hg.continuous.star.continuousOn).mul hf.continuous.continuousOn
  have hPr : IntervalIntegrable (fun r => radialMassFlux n z r*(star (deriv g r)*f r).re) volume 0 R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hR
    exact hV.mul (Complex.continuous_re.comp (hdg.star.mul hf.continuous)).continuousOn
  have hQr : IntervalIntegrable (fun r => radialMassDensity n z r*(star (g r)*f r).re) volume 0 R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hR
    exact hM.mul (Complex.continuous_re.comp (hg.continuous.star.mul hf.continuous)).continuousOn
  have hp : (∫ r in (0 : ℝ)..R, radialMassFlux n z r*(star (deriv g r)*f r).re) =
      (∫ r in (0 : ℝ)..R, (radialMassFlux n z r : ℂ)*star (deriv g r)*f r).re := by
    calc
      _ = ∫ r in (0 : ℝ)..R, Complex.reCLM ((radialMassFlux n z r : ℂ)*star (deriv g r)*f r) := by
        apply intervalIntegral.integral_congr
        intro r _
        simp only [Complex.reCLM_apply,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
        ring
      _ = _ := Complex.reCLM.intervalIntegral_comp_comm hP
  have hq : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(star (g r)*f r).re) =
      (∫ r in (0 : ℝ)..R, (radialMassDensity n z r : ℂ)*star (g r)*f r).re := by
    calc
      _ = ∫ r in (0 : ℝ)..R, Complex.reCLM ((radialMassDensity n z r : ℂ)*star (g r)*f r) := by
        apply intervalIntegral.integral_congr
        intro r _
        simp only [Complex.reCLM_apply,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
        ring
      _ = _ := Complex.reCLM.intervalIntegral_comp_comm hQ
  rw [radialMatched_dilation_pairing_boundary n z hX hz R hR f g hf hg]
  simp only [Complex.sub_re,Complex.ofReal_re]
  have hv : (∫ r in (0 : ℝ)..R, radialMassFlux n z r*(star (deriv g r)*f r).re+
      ((6-2*radialShootingA n)/2)*radialMassDensity n z r*(star (g r)*f r).re) =
      (∫ r in (0 : ℝ)..R, radialMassFlux n z r*(star (deriv g r)*f r).re)+
      ((6-2*radialShootingA n)/2)*(∫ r in (0 : ℝ)..R, radialMassDensity n z r*(star (g r)*f r).re) := by
    calc
      _ = ∫ r in (0 : ℝ)..R, radialMassFlux n z r*(star (deriv g r)*f r).re+
          ((6-2*radialShootingA n)/2)*(radialMassDensity n z r*(star (g r)*f r).re) := by
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = _ := by rw [intervalIntegral.integral_add hPr (hQr.const_mul _),intervalIntegral.integral_const_mul]
  rw [hv,hp,hq]

end DefocusingNLS

end OAI
