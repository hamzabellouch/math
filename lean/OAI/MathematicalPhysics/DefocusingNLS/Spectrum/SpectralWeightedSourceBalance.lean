import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedFluxBalance

namespace OAI

/-! The weak flux balance retains exactly the volume forcing of a first chain. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

private theorem integral_linear_six (R : ℝ) (f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℂ)
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃)
    (h₄ : Continuous f₄) (h₅ : Continuous f₅) (h₆ : Continuous f₆) (a b : ℂ) :
    (∫ r in (0 : ℝ)..R, f₁ r-f₂ r+a*f₃ r+f₄ r+b*f₅ r+f₆ r)=
      (∫ r in (0 : ℝ)..R, f₁ r)-(∫ r in (0 : ℝ)..R, f₂ r)+
      a*(∫ r in (0 : ℝ)..R, f₃ r)+(∫ r in (0 : ℝ)..R, f₄ r)+
      b*(∫ r in (0 : ℝ)..R, f₅ r)+(∫ r in (0 : ℝ)..R, f₆ r) := by
  rw [intervalIntegral.integral_add,intervalIntegral.integral_add,intervalIntegral.integral_add,
    intervalIntegral.integral_add,intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem spectralWeightedFlux_first_source_balance (R : ℝ) (hR : 0 ≤ R)
    (μ A P : ℝ → ℝ) (hμ : Continuous μ) (hA : Continuous A) (hP : Continuous P)
    (f g G : ℝ → ℂ) (hG : Continuous G) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (η c lam : ℂ) (φ : 𝓢(ℝ,ℂ))
    (hflux :
      (∫ r in (0 : ℝ)..R, star (deriv φ r)*spectralGaugeFirstFlux μ A f g r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*
        (η*(r : ℂ)^9*(μ r : ℂ)*f r+
          (r : ℂ)^11*(μ r : ℂ)*((P r : ℂ)*f r+(lam-c)*g r+G r)))=
      star (φ R)*spectralGaugeFirstFlux μ A f g R) :
    spectralClassicalRadialPairing R μ (deriv f) (deriv φ)+
      η*spectralClassicalAngularPairing R μ f φ+
      spectralClassicalRadialPairing R (fun r => μ r*P r) f φ+
      spectralClassicalRadialPairing R μ G φ=
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
      (r : ℂ)^11*(μ r : ℂ)*((P r : ℂ)*f r+(lam-c)*g r+G r)))
    (Continuous.intervalIntegrable (by unfold spectralGaugeFirstFlux; fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [← hsplit] at hflux
  have heq : (∫ r in (0 : ℝ)..R,
      star (deriv φ r)*spectralGaugeFirstFlux μ A f g r+
      star (φ r)*(η*(r : ℂ)^9*(μ r : ℂ)*f r+
        (r : ℂ)^11*(μ r : ℂ)*((P r : ℂ)*f r+(lam-c)*g r+G r)))=
      spectralClassicalRadialPairing R μ (deriv f) (deriv φ)-
      spectralClassicalRadialPairing R A g (deriv φ)+
      η*spectralClassicalAngularPairing R μ f φ+
      spectralClassicalRadialPairing R (fun r => μ r*P r) f φ+
      (lam-c)*spectralClassicalRadialPairing R μ g φ+
      spectralClassicalRadialPairing R μ G φ := by
    rw [spectralClassicalRadialPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR,
      spectralClassicalAngularPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR,
      spectralClassicalRadialPairing_interval R hR]
    rw [← integral_linear_six]
    · apply intervalIntegral.integral_congr
      intro r _
      simp only [spectralGaugeFirstFlux,Complex.ofReal_mul]
      ring
    all_goals fun_prop
  rw [heq] at hflux
  linear_combination hflux

theorem spectralWeightedFlux_second_source_balance (R : ℝ) (hR : 0 ≤ R)
    (μ A : ℝ → ℝ) (hμ : Continuous μ) (hA : Continuous A)
    (f g F : ℝ → ℂ) (hF : Continuous F) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (η c lam : ℂ) (φ : 𝓢(ℝ,ℂ))
    (hflux :
      (∫ r in (0 : ℝ)..R, star (deriv φ r)*spectralGaugeSecondFlux μ A f g r)+
      (∫ r in (0 : ℝ)..R, star (φ r)*
        (η*(r : ℂ)^9*(μ r : ℂ)*g r+
          (r : ℂ)^11*(μ r : ℂ)*((c-lam)*f r-F r)))=
      star (φ R)*spectralGaugeSecondFlux μ A f g R) :
    spectralClassicalRadialPairing R μ (deriv g) (deriv φ)+
      η*spectralClassicalAngularPairing R μ g φ+
      (c-lam)*spectralClassicalRadialPairing R μ f φ+
      spectralClassicalRadialPairing R A f (deriv φ)-
      spectralClassicalRadialPairing R μ F φ=
      star (φ R)*spectralGaugeSecondFlux μ A f g R := by
  have hflip : spectralGaugeFirstFlux μ (fun r => -A r) g f=
      spectralGaugeSecondFlux μ A f g := by
    funext r
    simp only [spectralGaugeFirstFlux,spectralGaugeSecondFlux,Complex.ofReal_neg,
      neg_mul,sub_neg_eq_add]
  have ht := spectralWeightedFlux_first_source_balance R hR μ (fun r => -A r) (fun _ => 0)
    hμ hA.neg continuous_const g f (fun r => -F r) hF.neg hg hf η (-c) (-lam) φ (by
      rw [hflip]
      simpa only [Complex.ofReal_zero,zero_mul,zero_add,neg_sub_neg,mul_assoc,sub_eq_add_neg,neg_neg,add_assoc,add_left_comm,add_comm,add_zero] using hflux)
  rw [hflip,spectralClassicalRadialPairing_neg_weight] at ht
  have hz : spectralClassicalRadialPairing R (fun r => μ r*0) g φ=0 := by
    simp only [spectralClassicalRadialPairing,mul_zero,zero_smul,integral_zero]
  rw [hz,add_zero] at ht
  have hn : spectralClassicalRadialPairing R μ (fun r => -F r) φ =
      -spectralClassicalRadialPairing R μ F φ := by
    simp only [spectralClassicalRadialPairing,smul_neg,mul_neg,integral_neg]
  rw [hn] at ht
  linear_combination ht

end DefocusingNLS

end OAI
