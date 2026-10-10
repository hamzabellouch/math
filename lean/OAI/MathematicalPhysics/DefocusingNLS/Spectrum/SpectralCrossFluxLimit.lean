import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeFluxIdentity

namespace OAI

/-! The pressure-free cross bound makes the total flux negligible on
the square-root frequency scale. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralCross_sqrt_frequency_limit (omega : ℕ → ℝ) (cross : ℕ → ℂ) (K : ℝ)
    (hw : Tendsto omega atTop atTop)
    (hcross : ∀ᶠ n in atTop, omega n*‖cross n‖ ≤ K) :
    Tendsto (fun n => Real.sqrt (omega n)*‖cross n‖) atTop (𝓝 0) := by
  have hnu := Real.tendsto_sqrt_atTop.comp hw
  have hzero : Tendsto (fun n => K/Real.sqrt (omega n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using (tendsto_inv_atTop_zero.comp hnu).const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))) _ hzero
  filter_upwards [hcross,hw.eventually (eventually_gt_atTop 0)] with n hn hwn
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hwn)).mpr
  calc
    _ = (Real.sqrt (omega n))^2*‖cross n‖ := by ring
    _ = omega n*‖cross n‖ := by rw [Real.sq_sqrt hwn.le]
    _ ≤ K := hn

theorem spectralCross_total_flux_limit (omega gamma flux : ℕ → ℝ) (cross : ℕ → ℂ) (K G : ℝ)
    (hG : 0 ≤ G) (hw : Tendsto omega atTop atTop)
    (hcross : ∀ᶠ n in atTop, omega n*‖cross n‖ ≤ K)
    (hgamma : ∀ᶠ n in atTop, |gamma n| ≤ G)
    (hflux : ∀ n, flux n = -4*gamma n*(cross n).im) :
    Tendsto (fun n => Real.sqrt (omega n)*flux n) atTop (𝓝 0) := by
  have hc := spectralCross_sqrt_frequency_limit omega cross K hw hcross
  have hb : ∀ᶠ n in atTop, ‖Real.sqrt (omega n)*flux n‖ ≤ (4*G)*(Real.sqrt (omega n)*‖cross n‖) := by
    filter_upwards [hgamma] with n hn
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),hflux n,abs_mul,abs_mul]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    have hi := Complex.abs_im_le_norm (cross n)
    calc
      _ ≤ Real.sqrt (omega n)*(4*G*‖cross n‖) := by gcongr
      _ = _ := by ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) hb (by simpa using hc.const_mul (4*G))

end DefocusingNLS

end OAI
