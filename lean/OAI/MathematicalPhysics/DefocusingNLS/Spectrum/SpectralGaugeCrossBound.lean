import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeCrossPairing

namespace OAI

/-! The pressure-free equation bounds the cross pairing independently of
the spectral frequency after multiplication by its imaginary part. -/

open Set Filter MeasureTheory
namespace DefocusingNLS

theorem spectralGaugeSecond_cross_bound (R C M L : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (mu A : ℝ → ℝ) (hmu : Continuous mu) (hA : Continuous A)
    (eta c : ℝ) (heta : 0 ≤ eta) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hmu0 : ∀ r ∈ Icc 0 R, 0 ≤ mu r)
    (hAbound : ∀ r ∈ Icc 0 R, |A r| ≤ C*mu r)
    (hflux : ∀ r ∈ Ioo 0 R, HasDerivAt (spectralGaugeSecondFlux mu A f g)
      ((eta : ℂ)*(r : ℂ)^9*(mu r : ℂ)*g r+(r : ℂ)^11*(mu r : ℂ)*((c : ℂ)-lam)*f r) r)
    (henergy : (∫ r in (0 : ℝ)..R,
      r^11*mu r*(‖f r‖^2+‖deriv g r‖^2)+eta*r^9*mu r*‖g r‖^2) ≤ M)
    (hboundary : ‖star (g R)*spectralGaugeSecondFlux mu A f g R‖ ≤ L) :
    |lam.im| *‖∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (g r)*f r‖ ≤ (1+C)*M+L := by
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdg := hg.continuous_deriv (by norm_num)
  let e := fun r : ℝ => r^11*mu r*(‖f r‖^2+‖deriv g r‖^2)+eta*r^9*mu r*‖g r‖^2
  let H := fun r : ℝ => ((r^11*mu r*‖deriv g r‖^2+eta*r^9*mu r*‖g r‖^2 : ℝ) : ℂ)+
    (r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r
  have hec : Continuous e := by dsimp only [e]; fun_prop
  have hHc : Continuous H := by dsimp only [H]; fun_prop
  have hpoint r (hr : r ∈ Icc 0 R) : ‖H r‖ ≤ (1+C)*e r := by
    have hmr := hmu0 r hr
    have hr11 : 0 ≤ r^11 := pow_nonneg hr.1 _
    have hr9 : 0 ≤ r^9 := pow_nonneg hr.1 _
    have hv : 0 ≤ r^11*mu r*‖deriv g r‖^2+eta*r^9*mu r*‖g r‖^2 := by positivity
    have ht : ‖(r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r‖ ≤
        C*(r^11*mu r)*(‖f r‖^2+‖deriv g r‖^2) := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr.1,norm_star]
      have hab := mul_le_mul_of_nonneg_left (hAbound r hr) hr11
      have hcross : ‖deriv g r‖*‖f r‖ ≤ ‖f r‖^2+‖deriv g r‖^2 := by
        nlinarith [sq_nonneg (‖f r‖-‖deriv g r‖),sq_nonneg ‖f r‖,sq_nonneg ‖deriv g r‖]
      calc
        _ = (r^11* |A r|)*(‖deriv g r‖*‖f r‖) := by ring
        _ ≤ (r^11*(C*mu r))*(‖f r‖^2+‖deriv g r‖^2) :=
          mul_le_mul hab hcross (by positivity) (by positivity)
        _ = _ := by ring
    have hn := norm_add_le (((r^11*mu r*‖deriv g r‖^2+eta*r^9*mu r*‖g r‖^2 : ℝ) : ℂ))
      ((r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv] at hn
    change ‖H r‖ ≤ _ at hn
    dsimp only [e]
    nlinarith [hn,ht,mul_nonneg hC (mul_nonneg (mul_nonneg (mul_nonneg heta hr9) hmr) (sq_nonneg ‖g r‖)),
      mul_nonneg (mul_nonneg hr11 hmr) (sq_nonneg ‖f r‖)]
  have hI : ‖∫ r in (0 : ℝ)..R, H r‖ ≤ (1+C)*M := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hR
      (Eventually.of_forall (fun r hr => hpoint r ⟨hr.1.le,hr.2⟩))
      ((hec.const_mul (1+C)).intervalIntegrable 0 R)
    rw [intervalIntegral.integral_const_mul] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hself := spectralGaugeSecond_self_pairing R hR mu A hmu hA (eta : ℂ) (c : ℂ) lam f g hf hg hflux
  have hsplit : (∫ r in (0 : ℝ)..R, H r) =
      ((∫ r in (0 : ℝ)..R, r^11*mu r*‖deriv g r‖^2 : ℝ) : ℂ)+
      (eta : ℂ)*((∫ r in (0 : ℝ)..R, r^9*mu r*‖g r‖^2 : ℝ) : ℂ)+
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(A r : ℂ)*star (deriv g r)*f r) := by
    dsimp only [H]
    simp_rw [show ∀ r : ℝ, eta*r^9*mu r*‖g r‖^2 = eta*(r^9*mu r*‖g r‖^2) by intro r; ring]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_ofReal,intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul]
    · push_cast
      rfl
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← hsplit] at hself
  calc
    _ ≤ ‖lam-(c : ℂ)‖*‖∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (g r)*f r‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using Complex.abs_im_le_norm (lam-(c : ℂ))
    _ = ‖(lam-(c : ℂ))*(∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (g r)*f r)‖ := (norm_mul _ _).symm
    _ ≤ (1+C)*M+L := by rw [hself]; exact (norm_sub_le _ _).trans (add_le_add hI hboundary)

end DefocusingNLS

end OAI
