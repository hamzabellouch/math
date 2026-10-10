import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeCrossPairing

namespace OAI

/-! The pressure-free gauge equation tested against an arbitrary smooth
component; choosing the first component controls its L2 mass. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralGaugeSecond_test_pairing (R : ℝ) (hR : 0 ≤ R)
    (mu A : ℝ → ℝ) (hmu : Continuous mu) (hA : Continuous A)
    (eta c lam : ℂ) (f g phi : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hphi : ContDiff ℝ 1 phi)
    (hflux : ∀ r ∈ Ioo 0 R, HasDerivAt (spectralGaugeSecondFlux mu A f g)
      (eta*(r : ℂ)^9*(mu r : ℂ)*g r+(r : ℂ)^11*(mu r : ℂ)*(c-lam)*f r) r) :
    (lam-c)*(∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (phi r)*f r) =
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (deriv phi r)*deriv g r)+
      eta*(∫ r in (0 : ℝ)..R, (r : ℂ)^9*(mu r : ℂ)*star (phi r)*g r)+
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(A r : ℂ)*star (deriv phi r)*f r)-
      star (phi R)*spectralGaugeSecondFlux mu A f g R := by
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdg := hg.continuous_deriv (by norm_num)
  have hpc := hphi.continuous
  have hdpc := hphi.continuous_deriv (by norm_num)
  let F := spectralGaugeSecondFlux mu A f g
  let H := fun r : ℝ => eta*(r : ℂ)^9*(mu r : ℂ)*g r+(r : ℂ)^11*(mu r : ℂ)*(c-lam)*f r
  have hFc : Continuous F := by
    change Continuous (fun r : ℝ => (r : ℂ)^11*((mu r : ℂ)*deriv g r+(A r : ℂ)*f r))
    fun_prop
  have hHc : Continuous H := by dsimp only [H]; fun_prop
  have ht := spectralClassicalFlux_continuous_test R hR F H phi hFc.continuousOn hHc.continuousOn
    hflux (by simp [F,spectralGaugeSecondFlux]) hphi
  let D := fun r : ℝ => (r : ℂ)^11*(mu r : ℂ)*star (deriv phi r)*deriv g r
  let G := fun r : ℝ => (r : ℂ)^9*(mu r : ℂ)*star (phi r)*g r
  let T := fun r : ℝ => (r : ℂ)^11*(A r : ℂ)*star (deriv phi r)*f r
  let V := fun r : ℝ => (r : ℂ)^11*(mu r : ℂ)*star (phi r)*f r
  have hDc : Continuous D := by dsimp only [D]; fun_prop
  have hGc : Continuous G := by dsimp only [G]; fun_prop
  have hTc : Continuous T := by dsimp only [T]; fun_prop
  have hVc : Continuous V := by dsimp only [V]; fun_prop
  have hp (r : ℝ) : star (deriv phi r)*F r+star (phi r)*H r =
      D r+eta*G r+T r-(lam-c)*V r := by
    dsimp only [D,G,T,V,F,H,spectralGaugeSecondFlux]
    ring
  have ht' : (∫ r in (0 : ℝ)..R, D r+eta*G r+T r-(lam-c)*V r) = star (phi R)*F R := by
    rw [← intervalIntegral.integral_add] at ht
    · simpa only [hp] using ht
    · exact (hdpc.star.mul hFc).intervalIntegrable 0 R
    · exact (hpc.star.mul hHc).intervalIntegrable 0 R
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,
    intervalIntegral.integral_add,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at ht'
  · dsimp only [D,G,T,V,F] at ht'
    linear_combination -ht'
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

end DefocusingNLS

end OAI
