import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexVirial
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexGaugeAction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDilationPairing

namespace OAI

/-! The actual coupled eigenvalue equation tested against the shifted dilation.
The bulk scalar forms retain their exact outer boundary contribution. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialComplexDilationPairing (n : ℕ) (z : ProfileMatchingBall)
    (R s : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ r in (0 : ℝ)..R, (radialMassDensity n z r : ℂ)*
    spectralDilationCross (radialMatchedVelocity n z r) s (f r) (g r) (deriv f r) (deriv g r)

theorem radialMatched_complex_dilation_identity (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R s : ℝ) (hR : 0 ≤ R) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) (eta : ℂ) lam f g) :
    (s*radialComplexAngularForm n z eta R (radialSpectralPressure n z) f+
      radialComplexAngularVirial n z eta R (radialSpectralPressure n z) (deriv (radialSpectralPressure n z)) f+
      radialComplexAngularBoundary n z eta R s (radialSpectralPressure n z) f)+
    (s*radialComplexAngularForm n z eta R (fun _ => 0) g+
      radialComplexAngularVirial n z eta R (fun _ => 0) (fun _ => 0) g+
      radialComplexAngularBoundary n z eta R s (fun _ => 0) g) =
      ((lam-(s : ℂ))*radialComplexDilationPairing n z R s f g).re := by
  have hq := (radialSpectralPressure_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hdq := radialSpectralPressure_deriv_continuousOn n z hX hz R
  have hF := radialComplexAngular_virial_identity n z hX hz eta R s hR _ _ hq hdq
    (fun r _ => radialSpectralPressure_hasDerivAt n z hX hz r) f hf
  have hG := radialComplexAngular_virial_identity n z hX hz eta R s hR
    (fun _ => 0) (fun _ => 0) continuousOn_const continuousOn_const
    (fun r _ => hasDerivAt_const r 0) g hg
  let I := fun r : ℝ => (radialMassDensity n z r : ℂ)*
    spectralDilationCross (radialMatchedVelocity n z r) s (f r) (g r) (deriv f r) (deriv g r)
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdf := hf.continuous_deriv (by norm_num)
  have hdg := hg.continuous_deriv (by norm_num)
  have hddf := (hf.deriv' (n := 1)).continuous_deriv (by norm_num)
  have hddg := (hg.deriv' (n := 1)).continuous_deriv (by norm_num)
  have hm := (radialMassDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hms := radialMassSlope_continuousOn n z hX hz R
  have hw := radialMatchedVelocity_continuousOn n z hX hz R
  have ha := (radialAngularDensity_continuous n z hX hz).continuousOn (s := Icc 0 R)
  have hIc : ContinuousOn I (Icc 0 R) := by dsimp only [I,spectralDilationCross]; fun_prop
  have hAF : ContinuousOn (radialComplexAngularAction n z eta (radialSpectralPressure n z) f) (Icc 0 R) := by
    change ContinuousOn (fun r => -(radialMassDensity n z r : ℂ)*deriv (deriv f) r-
      (radialMassSlope n z r : ℂ)*deriv f r+
      (radialMassDensity n z r*radialSpectralPressure n z r+eta*radialAngularDensity n z r : ℝ)*f r) (Icc 0 R)
    fun_prop
  have hAG : ContinuousOn (radialComplexAngularAction n z eta (fun _ => 0) g) (Icc 0 R) := by
    change ContinuousOn (fun r => -(radialMassDensity n z r : ℂ)*deriv (deriv g) r-
      (radialMassSlope n z r : ℂ)*deriv g r+
      (radialMassDensity n z r*0+eta*radialAngularDensity n z r : ℝ)*g r) (Icc 0 R)
    fun_prop
  have hTF : ContinuousOn (radialComplexTest n z s f) (Icc 0 R) := by
    change ContinuousOn (fun r => (s : ℂ)*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r) (Icc 0 R)
    fun_prop
  have hTG : ContinuousOn (radialComplexTest n z s g) (Icc 0 R) := by
    change ContinuousOn (fun r => (s : ℂ)*g r+(radialMatchedVelocity n z r : ℂ)*deriv g r) (Icc 0 R)
    fun_prop
  have hFI : IntervalIntegrable (fun r => (star (radialComplexTest n z s f r)*
      radialComplexAngularAction n z eta (radialSpectralPressure n z) f r).re) volume 0 R :=
    (Complex.continuous_re.comp_continuousOn (hTF.star.mul hAF)).intervalIntegrable_of_Icc hR
  have hGI : IntervalIntegrable (fun r => (star (radialComplexTest n z s g r)*
      radialComplexAngularAction n z eta (fun _ => 0) g r).re) volume 0 R :=
    (Complex.continuous_re.comp_continuousOn (hTG.star.mul hAG)).intervalIntegrable_of_Icc hR
  rw [← hF,← hG,← intervalIntegral.integral_add hFI hGI]
  have hpoint r (hr : r ∈ Icc 0 R) :
      (star (radialComplexTest n z s f r)*radialComplexAngularAction n z eta (radialSpectralPressure n z) f r).re+
      (star (radialComplexTest n z s g r)*radialComplexAngularAction n z eta (fun _ => 0) g r).re =
        ((lam-(s : ℂ))*I r).re := by
    by_cases hr0 : r=0
    · simp [hr0,I,radialComplexAngularAction,radialMassDensity,radialMassSlope,radialAngularDensity]
    · obtain ⟨hAf,hAg⟩ := radialMatched_complex_action n z hX hz eta lam f g hf hg he r
        (lt_of_le_of_ne hr.1 (Ne.symm hr0))
      rw [hAf,hAg,← Complex.add_re]
      dsimp only [radialComplexTest,I]
      rw [show star ((s : ℂ)*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r)*
          (-(radialMassDensity n z r : ℂ)*(lam*g r+(radialMatchedVelocity n z r : ℂ)*deriv g r))+
          star ((s : ℂ)*g r+(radialMatchedVelocity n z r : ℂ)*deriv g r)*
          ((radialMassDensity n z r : ℂ)*(lam*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r)) =
        (radialMassDensity n z r : ℂ)*(star ((s : ℂ)*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r)*
          (-lam*g r-(radialMatchedVelocity n z r : ℂ)*deriv g r)+
          star ((s : ℂ)*g r+(radialMatchedVelocity n z r : ℂ)*deriv g r)*
          (lam*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r)) by ring]
      rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        spectralDilationCross_skew]
      rw [show (lam-(s : ℂ))*((radialMassDensity n z r : ℂ)*
          spectralDilationCross (radialMatchedVelocity n z r) s (f r) (g r) (deriv f r) (deriv g r)) =
        (radialMassDensity n z r : ℂ)*((lam-(s : ℂ))*
          spectralDilationCross (radialMatchedVelocity n z r) s (f r) (g r) (deriv f r) (deriv g r)) by ring]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hIint := hIc.intervalIntegrable_of_Icc (μ := volume) hR
  have hRe : (∫ r in (0 : ℝ)..R, ((lam-(s : ℂ))*I r).re) =
      ((∫ r in (0 : ℝ)..R, (lam-(s : ℂ))*I r)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hIint.const_mul _)
  calc
    _ = ∫ r in (0 : ℝ)..R, ((lam-(s : ℂ))*I r).re := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hpoint r (by simpa only [uIcc_of_le hR] using hr)
    _ = _ := by rw [hRe,intervalIntegral.integral_const_mul]; rfl

end DefocusingNLS

end OAI
