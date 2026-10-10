import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalContinuousTest

namespace OAI

/-! Testing the pressure-free gauge equation against its second component
gives the exact cross-pairing identity used in Case II. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralGaugeSecond_self_pairing (R : ℝ) (hR : 0 ≤ R)
    (mu A : ℝ → ℝ) (hmu : Continuous mu) (hA : Continuous A)
    (eta c lam : ℂ) (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hflux : ∀ r ∈ Ioo 0 R, HasDerivAt (spectralGaugeSecondFlux mu A f g)
      (eta*(r : ℂ)^9*(mu r : ℂ)*g r+(r : ℂ)^11*(mu r : ℂ)*(c-lam)*f r) r) :
    (lam-c)*(∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (g r)*f r) =
      ((∫ r in (0 : ℝ)..R, r^11*mu r*‖deriv g r‖^2 : ℝ) : ℂ)+
      eta*((∫ r in (0 : ℝ)..R, r^9*mu r*‖g r‖^2 : ℝ) : ℂ)+
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r)-
      star (g R)*spectralGaugeSecondFlux mu A f g R := by
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdg := hg.continuous_deriv (by norm_num)
  let F := spectralGaugeSecondFlux mu A f g
  let H := fun r : ℝ => eta*(r : ℂ)^9*(mu r : ℂ)*g r+(r : ℂ)^11*(mu r : ℂ)*(c-lam)*f r
  have hFc : Continuous F := by
    change Continuous (fun r : ℝ => (r : ℂ)^11*((mu r : ℂ)*deriv g r+(A r : ℂ)*f r))
    fun_prop
  have hHc : Continuous H := by dsimp only [H]; fun_prop
  have ht := spectralClassicalFlux_continuous_test R hR F H g hFc.continuousOn hHc.continuousOn
    hflux (by simp [F,spectralGaugeSecondFlux]) (hg.of_le (by norm_num))
  let D := fun r : ℝ => ((r^11*mu r*‖deriv g r‖^2 : ℝ) : ℂ)
  let G := fun r : ℝ => ((r^9*mu r*‖g r‖^2 : ℝ) : ℂ)
  let T := fun r : ℝ => (r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r
  let C := fun r : ℝ => (r : ℂ)^11*(mu r : ℂ)*star (g r)*f r
  have hDc : Continuous D := by dsimp only [D]; fun_prop
  have hGc : Continuous G := by dsimp only [G]; fun_prop
  have hTc : Continuous T := by dsimp only [T]; fun_prop
  have hCc : Continuous C := by dsimp only [C]; fun_prop
  have hn (z : ℂ) : star z*z = ((‖z‖^2 : ℝ) : ℂ) := by
    simp only [Complex.star_def,Complex.conj_mul',Complex.ofReal_pow]
  have hp (r : ℝ) : star (deriv g r)*F r+star (g r)*H r =
      D r+eta*G r+T r-(lam-c)*C r := by
    dsimp only [D,G,T,C,F,H,spectralGaugeSecondFlux]
    push_cast
    calc
      _ = (r : ℂ)^11*(mu r : ℂ)*(star (deriv g r)*deriv g r)+
          eta*((r : ℂ)^9*(mu r : ℂ)*(star (g r)*g r))+
          (r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r-
          (lam-c)*((r : ℂ)^11*(mu r : ℂ)*star (g r)*f r) := by ring
      _ = _ := by rw [hn,hn]; simp only [Complex.ofReal_pow]
  have ht' : (∫ r in (0 : ℝ)..R, D r+eta*G r+T r-(lam-c)*C r) = star (g R)*F R := by
    rw [← intervalIntegral.integral_add] at ht
    · simpa only [hp] using ht
    · exact (hdg.star.mul hFc).intervalIntegrable 0 R
    · exact (hgc.star.mul hHc).intervalIntegrable 0 R
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,
    intervalIntegral.integral_add,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at ht'
  · dsimp only [D,G,T,C] at ht'
    rw [intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal] at ht'
    linear_combination -ht'
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem radialMatchedGauge_cross_pairing (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R) (eta lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) eta lam f g) :
    let mu := radialMatchedMassFunction n z
    let A := radialMatchedTransportFunction n z
    (lam-((6-2*radialShootingA n : ℝ) : ℂ))*
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (g r)*f r) =
      ((∫ r in (0 : ℝ)..R, r^11*mu r*‖deriv g r‖^2 : ℝ) : ℂ)+
      eta*((∫ r in (0 : ℝ)..R, r^9*mu r*‖g r‖^2 : ℝ) : ℂ)+
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r)-
      star (g R)*spectralGaugeSecondFlux mu A f g R := by
  apply spectralGaugeSecond_self_pairing R hR.le _ _
    (radialMatchedMassFunction_continuous n z hX hz)
    (radialMatchedTransportFunction_continuous n z hX hz) _ _ _ f g hf hg
  intro r hr
  exact (radialMatchedGauge_flux n z hX hz eta lam f g hf hg he r hr.1).2

end DefocusingNLS

end OAI
