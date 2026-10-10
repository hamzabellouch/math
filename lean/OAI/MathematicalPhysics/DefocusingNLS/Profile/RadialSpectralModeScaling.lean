import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! Constant nonzero scaling preserves every classical and outgoing condition
of an actual radial mode and scales its fixed-ball energy quadratically. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def RadialSpectralMode.scale {a b : ℝ} {m N : ℕ} {Q : ℝ → ℂ} {eta lam : ℂ}
    (u : RadialSpectralMode a b m N Q eta lam) (c : ℂ) (hc : c ≠ 0) :
    RadialSpectralMode a b m N Q eta lam where
  first := fun r => c*u.first r
  second := fun r => c*u.second r
  first_c2 := contDiff_const.mul u.first_c2
  second_c2 := contDiff_const.mul u.second_c2
  equation := by
    intro r hr
    obtain ⟨h1,h2⟩ := u.equation r hr
    dsimp only
    simp only [deriv_const_mul_field',deriv_const_mul_field]
    constructor
    · linear_combination c*h1
    · linear_combination c*h2
  first_smooth := contDiffOn_const.mul u.first_smooth
  second_smooth := contDiffOn_const.mul u.second_smooth
  first_top := by
    have hi := u.first_top.const_mul (‖c‖^2)
    apply MeasureTheory.Integrable.congr hi
    filter_upwards [] with r
    simp only [iteratedDeriv_const_mul_field,norm_mul,mul_pow]
    ring
  second_top := by
    have hi := u.second_top.const_mul (‖c‖^2)
    apply MeasureTheory.Integrable.congr hi
    filter_upwards [] with r
    simp only [iteratedDeriv_const_mul_field,norm_mul,mul_pow]
    ring
  bounded := by
    obtain ⟨M,hM,hb⟩ := u.bounded
    refine ⟨‖c‖*M,mul_nonneg (norm_nonneg _) hM,fun r => ?_⟩
    change ‖c • (u.first r,u.second r)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hb r) (norm_nonneg c)
  nonzero := by
    obtain ⟨r,hr,hn⟩ := u.nonzero
    refine ⟨r,hr,?_⟩
    rcases hn with hn | hn
    · exact Or.inl (mul_ne_zero hc hn)
    · exact Or.inr (mul_ne_zero hc hn)

theorem spectralRadialEnergyDensity_scale (eta : ℝ) (f g : ℝ → ℂ) (c : ℂ) (r : ℝ) :
    spectralRadialEnergyDensity eta (fun t => c*f t) (fun t => c*g t) r =
      ‖c‖^2*spectralRadialEnergyDensity eta f g r := by
  dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
  simp only [deriv_const_mul_field,norm_mul,mul_pow]
  ring

theorem spectralRadialEnergyIntegral_scale (eta R : ℝ) (f g : ℝ → ℂ) (c : ℂ) :
    (∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta (fun t => c*f t) (fun t => c*g t) r) =
      ‖c‖^2*(∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta f g r) := by
  simp_rw [spectralRadialEnergyDensity_scale]
  exact intervalIntegral.integral_const_mul _ _

end DefocusingNLS

end OAI
