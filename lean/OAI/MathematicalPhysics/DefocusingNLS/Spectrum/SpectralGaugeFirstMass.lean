import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeSecondTest
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! Testing the pressure-free equation against the first component yields
an inverse-frequency bound for its weighted L2 mass. -/

open Set MeasureTheory
namespace DefocusingNLS

private theorem norm_product_le_squares (x y : ℂ) : ‖x‖*‖y‖ ≤ ‖x‖^2+‖y‖^2 := by
  nlinarith [sq_nonneg (‖x‖-‖y‖),sq_nonneg ‖x‖,sq_nonneg ‖y‖]

theorem spectralGaugeSecond_test_source_bound (eta r mu A C : ℝ)
    (heta : 0 ≤ eta) (hr : 0 ≤ r) (hmu : 0 ≤ mu) (hC : 0 ≤ C) (hA : |A| ≤ C*mu)
    (f g : ℝ → ℂ) :
    ‖(r : ℂ)^11*(mu : ℂ)*star (deriv f r)*deriv g r+
      (eta : ℂ)*(r : ℂ)^9*(mu : ℂ)*star (f r)*g r+
      (r : ℂ)^11*(A : ℂ)*star (deriv f r)*f r‖ ≤
        (1+C)*mu*spectralRadialEnergyDensity eta f g r := by
  have hd := norm_product_le_squares (deriv f r) (deriv g r)
  have hv := norm_product_le_squares (f r) (g r)
  have ht := norm_product_le_squares (deriv f r) (f r)
  have hD : ‖(r : ℂ)^11*(mu : ℂ)*star (deriv f r)*deriv g r‖ ≤
      r^11*mu*(‖deriv f r‖^2+‖deriv g r‖^2) := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,
      abs_of_nonneg hmu,norm_star]
    nlinarith only [mul_le_mul_of_nonneg_left hd (mul_nonneg (pow_nonneg hr 11) hmu)]
  have hG : ‖(eta : ℂ)*(r : ℂ)^9*(mu : ℂ)*star (f r)*g r‖ ≤
      eta*r^9*mu*(‖f r‖^2+‖g r‖^2) := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,
      abs_of_nonneg hmu,abs_of_nonneg heta,norm_star]
    nlinarith only [mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ eta*r^9*mu)]
  have hT : ‖(r : ℂ)^11*(A : ℂ)*star (deriv f r)*f r‖ ≤
      C*(r^11*mu)*(‖f r‖^2+‖deriv f r‖^2) := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,norm_star]
    have hb := mul_le_mul hA ht (by positivity) (mul_nonneg hC hmu)
    have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hr 11)
    nlinarith only [hb']
  have hn := (norm_add_le ((r : ℂ)^11*(mu : ℂ)*star (deriv f r)*deriv g r+
    (eta : ℂ)*(r : ℂ)^9*(mu : ℂ)*star (f r)*g r)
    ((r : ℂ)^11*(A : ℂ)*star (deriv f r)*f r)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hrest : 0 ≤ C*(r^11*mu)*(‖g r‖^2+‖deriv g r‖^2)+
      C*(eta*r^9*mu)*(‖f r‖^2+‖g r‖^2)+r^11*mu*(‖f r‖^2+‖g r‖^2) := by positivity
  dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
  nlinarith only [hn,hD,hG,hT,hrest]

theorem spectralGaugeFirst_mass_bound (R C M L : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (mu A : ℝ → ℝ) (hmu : Continuous mu) (hA : Continuous A)
    (eta c : ℝ) (heta : 0 ≤ eta) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hmu0 : ∀ r ∈ Icc 0 R, 0 ≤ mu r) (hAbound : ∀ r ∈ Icc 0 R, |A r| ≤ C*mu r)
    (hflux : ∀ r ∈ Ioo 0 R, HasDerivAt (spectralGaugeSecondFlux mu A f g)
      ((eta : ℂ)*(r : ℂ)^9*(mu r : ℂ)*g r+(r : ℂ)^11*(mu r : ℂ)*((c : ℂ)-lam)*f r) r)
    (henergy : (∫ r in (0 : ℝ)..R, mu r*spectralRadialEnergyDensity eta f g r) ≤ M)
    (hboundary : ‖star (f R)*spectralGaugeSecondFlux mu A f g R‖ ≤ L) :
    |lam.im| *(∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2) ≤ (1+C)*M+L := by
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hdf := hf.continuous_deriv (by norm_num)
  have hdg := hg.continuous_deriv (by norm_num)
  let D := fun r : ℝ => (r : ℂ)^11*(mu r : ℂ)*star (deriv f r)*deriv g r
  let G := fun r : ℝ => (eta : ℂ)*(r : ℂ)^9*(mu r : ℂ)*star (f r)*g r
  let T := fun r : ℝ => (r : ℂ)^11*(A r : ℂ)*star (deriv f r)*f r
  let H := fun r => D r+G r+T r
  let E := fun r => mu r*spectralRadialEnergyDensity eta f g r
  have hDc : Continuous D := by dsimp only [D]; fun_prop
  have hGc : Continuous G := by dsimp only [G]; fun_prop
  have hTc : Continuous T := by dsimp only [T]; fun_prop
  have hHc : Continuous H := hDc.add hGc |>.add hTc
  have hEc : Continuous E := hmu.mul (spectralRadialEnergyDensity_continuous eta f g hf hg)
  have hI : ‖∫ r in (0 : ℝ)..R, H r‖ ≤ (1+C)*M := by
    have hpoint r (hr : r ∈ Ioc 0 R) : ‖H r‖ ≤ (1+C)*E r := by
      simpa only [H,D,G,T,E,mul_assoc] using
        spectralGaugeSecond_test_source_bound eta r (mu r) (A r) C heta hr.1.le
          (hmu0 r ⟨hr.1.le,hr.2⟩) hC (hAbound r ⟨hr.1.le,hr.2⟩) f g
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hR
      (Filter.Eventually.of_forall hpoint)
      ((hEc.const_mul (1+C)).intervalIntegrable 0 R)
    rw [intervalIntegral.integral_const_mul] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have ht := spectralGaugeSecond_test_pairing R hR mu A hmu hA (eta : ℂ) (c : ℂ) lam f g f hf hg
    (hf.of_le (by norm_num)) hflux
  have hmass : (∫ r in (0 : ℝ)..R, (r : ℂ)^11*(mu r : ℂ)*star (f r)*f r) =
      ((∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    have hn : star (f r)*f r = ((‖f r‖^2 : ℝ) : ℂ) := by
      simp only [Complex.star_def,Complex.conj_mul',Complex.ofReal_pow]
    push_cast
    calc
      _ = (r : ℂ)^11*(mu r : ℂ)*(star (f r)*f r) := by ring
      _ = _ := by rw [hn]; push_cast; ring
  have hsplit : (∫ r in (0 : ℝ)..R, H r) =
      (∫ r in (0 : ℝ)..R, D r)+
      (eta : ℂ)*(∫ r in (0 : ℝ)..R, (r : ℂ)^9*(mu r : ℂ)*star (f r)*g r)+
      (∫ r in (0 : ℝ)..R, T r) := by
    dsimp only [H,G]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_add]
    · rw [← intervalIntegral.integral_const_mul]
      congr 2
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hmass,← hsplit] at ht
  have hmass0 : 0 ≤ ∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2 := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hm := hmu0 r hr
    have hr0 := hr.1
    positivity
  calc
    _ ≤ ‖lam-(c : ℂ)‖*(∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2) := by
      apply mul_le_mul_of_nonneg_right _ hmass0
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using Complex.abs_im_le_norm (lam-(c : ℂ))
    _ = ‖(lam-(c : ℂ))*((∫ r in (0 : ℝ)..R, r^11*mu r*‖f r‖^2 : ℝ) : ℂ)‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hmass0]
    _ ≤ (1+C)*M+L := by rw [ht]; exact (norm_sub_le _ _).trans (add_le_add hI hboundary)

end DefocusingNLS

end OAI
