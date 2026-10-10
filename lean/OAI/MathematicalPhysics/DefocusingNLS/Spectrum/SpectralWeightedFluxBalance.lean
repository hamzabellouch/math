import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalTestForms
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularComplexIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalFluxTesting
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeClassicalFlux

namespace OAI

/-! The dimension-twelve classical flux identity in the exact weighted test form. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralClassicalRadialPairing_interval (R : ℝ) (hR : 0 ≤ R)
    (q : ℝ → ℝ) (f φ : ℝ → ℂ) :
    spectralClassicalRadialPairing R q f φ=
      ∫ r in (0 : ℝ)..R, (r : ℂ)^11*star (φ r)*(q r : ℂ)*f r := by
  rw [spectralClassicalRadialPairing,spectral_radial_complex_integral R hR]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Complex.real_smul]
  ring

theorem spectralClassicalAngularPairing_interval (R : ℝ) (hR : 0 ≤ R)
    (q : ℝ → ℝ) (f φ : ℝ → ℂ) :
    spectralClassicalAngularPairing R q f φ=
      ∫ r in (0 : ℝ)..R, (r : ℂ)^9*star (φ r)*(q r : ℂ)*f r := by
  rw [spectralClassicalAngularPairing,spectral_angular_complex_integral R hR]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Complex.real_smul]
  ring

private theorem integral_linear_five (R : ℝ) (f₁ f₂ f₃ f₄ f₅ : ℝ → ℂ)
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃)
    (h₄ : Continuous f₄) (h₅ : Continuous f₅) (a b : ℂ) :
    (∫ r in (0 : ℝ)..R, f₁ r-f₂ r+a*f₃ r+f₄ r+b*f₅ r)=
      (∫ r in (0 : ℝ)..R, f₁ r)-(∫ r in (0 : ℝ)..R, f₂ r)+
      a*(∫ r in (0 : ℝ)..R, f₃ r)+(∫ r in (0 : ℝ)..R, f₄ r)+
      b*(∫ r in (0 : ℝ)..R, f₅ r) := by
  rw [intervalIntegral.integral_add,intervalIntegral.integral_add,
    intervalIntegral.integral_add,intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem spectralWeightedFlux_first_balance (R : ℝ) (hR : 0 ≤ R)
    (μ A P : ℝ → ℝ) (hμ : Continuous μ) (hA : Continuous A) (hP : Continuous P)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (η c lam : ℂ) (φ : 𝓢(ℝ,ℂ))
    (hflux :
      (∫ r in (0 : ℝ)..R, star (deriv φ r)*spectralGaugeFirstFlux μ A f g r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*
        (η*(r : ℂ)^9*(μ r : ℂ)*f r+
          (r : ℂ)^11*(μ r : ℂ)*((P r : ℂ)*f r+(lam-c)*g r)))=
      star (φ R)*spectralGaugeFirstFlux μ A f g R) :
    spectralClassicalRadialPairing R μ (deriv f) (deriv φ)+
      η*spectralClassicalAngularPairing R μ f φ+
      spectralClassicalRadialPairing R (fun r => μ r*P r) f φ=
      (c-lam)*spectralClassicalRadialPairing R μ g φ+
      spectralClassicalRadialPairing R A g (deriv φ)+
      star (φ R)*spectralGaugeFirstFlux μ A f g R := by
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdf := hf.continuous_deriv (by norm_num)
  have hdφ : Continuous (deriv (φ : ℝ → ℂ)) :=
    (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  have hsplit := intervalIntegral.integral_add (μ := volume)
    (a := (0 : ℝ)) (b := R)
    (f := fun r => star (deriv φ r)*spectralGaugeFirstFlux μ A f g r)
    (g := fun r => star (φ r)*(η*(r : ℂ)^9*(μ r : ℂ)*f r+
      (r : ℂ)^11*(μ r : ℂ)*((P r : ℂ)*f r+(lam-c)*g r)))
    (Continuous.intervalIntegrable (by unfold spectralGaugeFirstFlux; fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [← hsplit] at hflux
  have heq : (∫ r in (0 : ℝ)..R,
      star (deriv φ r)*spectralGaugeFirstFlux μ A f g r+
      star (φ r)*(η*(r : ℂ)^9*(μ r : ℂ)*f r+
        (r : ℂ)^11*(μ r : ℂ)*((P r : ℂ)*f r+(lam-c)*g r)))=
      spectralClassicalRadialPairing R μ (deriv f) (deriv φ)-
      spectralClassicalRadialPairing R A g (deriv φ)+
      η*spectralClassicalAngularPairing R μ f φ+
      spectralClassicalRadialPairing R (fun r => μ r*P r) f φ+
      (lam-c)*spectralClassicalRadialPairing R μ g φ := by
    rw [spectralClassicalRadialPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR,
      spectralClassicalAngularPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR]
    rw [← integral_linear_five]
    · apply intervalIntegral.integral_congr
      intro r _
      simp only [spectralGaugeFirstFlux,Complex.ofReal_mul]
      ring
    all_goals fun_prop
  rw [heq] at hflux
  linear_combination hflux

theorem spectralClassicalRadialPairing_neg_weight (R : ℝ) (q : ℝ → ℝ)
    (f φ : ℝ → ℂ) :
    spectralClassicalRadialPairing R (fun r => -q r) f φ=
      -spectralClassicalRadialPairing R q f φ := by
  unfold spectralClassicalRadialPairing
  simp only [neg_smul,mul_neg,integral_neg]

theorem spectralWeightedFlux_second_balance (R : ℝ) (hR : 0 ≤ R)
    (μ A : ℝ → ℝ) (hμ : Continuous μ) (hA : Continuous A)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (η c lam : ℂ) (φ : 𝓢(ℝ,ℂ))
    (hflux :
      (∫ r in (0 : ℝ)..R, star (deriv φ r)*spectralGaugeSecondFlux μ A f g r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*
        (η*(r : ℂ)^9*(μ r : ℂ)*g r+
          (r : ℂ)^11*(μ r : ℂ)*(c-lam)*f r))=
      star (φ R)*spectralGaugeSecondFlux μ A f g R) :
    spectralClassicalRadialPairing R μ (deriv g) (deriv φ)+
      η*spectralClassicalAngularPairing R μ g φ+
      (c-lam)*spectralClassicalRadialPairing R μ f φ+
      spectralClassicalRadialPairing R A f (deriv φ)=
      star (φ R)*spectralGaugeSecondFlux μ A f g R := by
  have hflip : spectralGaugeFirstFlux μ (fun r => -A r) g f=
      spectralGaugeSecondFlux μ A f g := by
    funext r
    simp only [spectralGaugeFirstFlux,spectralGaugeSecondFlux,Complex.ofReal_neg,
      neg_mul,sub_neg_eq_add]
  have ht := spectralWeightedFlux_first_balance R hR μ (fun r => -A r) (fun _ => 0)
    hμ hA.neg continuous_const g f hg hf η (-c) (-lam) φ (by
      rw [hflip]
      simpa only [Complex.ofReal_zero,zero_mul,zero_add,neg_sub_neg,mul_assoc] using hflux)
  rw [hflip,spectralClassicalRadialPairing_neg_weight] at ht
  have hz : spectralClassicalRadialPairing R (fun r => μ r*0) g φ=0 := by
    simp only [spectralClassicalRadialPairing,mul_zero,zero_smul,integral_zero]
  rw [hz,add_zero] at ht
  linear_combination ht

end DefocusingNLS

end OAI
