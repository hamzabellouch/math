import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningConeError

namespace OAI

/-! Every fixed cutoff at least 32 gives a uniform bound for the forbidden
residual. This bounds the Green constant along an escaping parameter sequence. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralTurningCutoffError_le (M : ℝ) (hM : 32 ≤ M) :
    spectralTurningCutoffError M ≤ 5/24 := by
  have hs : 2 ≤ Real.sqrt (M/8) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    linarith
  change 5/(3*(Real.sqrt (M/8))^3) ≤ 5/24
  apply (div_le_iff₀ (by positivity : 0 < 3*(Real.sqrt (M/8))^3)).mpr
  have hp : (8 : ℝ) ≤ (Real.sqrt (M/8))^3 := by
    calc
      _ = (2 : ℝ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hs 3
  nlinarith

theorem spectralTurning_eventual_residual_bound
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (R M : ℝ) (hR : 0 < R) (hM : 32 ≤ M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1) :
    ∀ᶠ n in atTop,
      (∫ t in R..(r₀ n-M*d n), (25/4 : ℝ)*
        ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
          ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖) ≤ 2 := by
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  have hbound := (spectralTurningNegativeError_tendsto M R r₀ d hr₀ hd).const_mul (25/4 : ℝ)
  have hlim : (25/4 : ℝ)*spectralTurningCutoffError M < 2 := by
    linarith [spectralTurningCutoffError_le M hM]
  filter_upwards [hdata,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hr₀.eventually (eventually_ge_atTop (max (2*R) (2*M))),
    hbound.eventually (gt_mem_nhds hlim)] with n hn hdn hrn hbn
  rcases hn with ⟨hrp,hd0,heta,hz,hsc⟩
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hd0
    intro he
    rw [← he] at hsc
    norm_num at hsc
  have hMp : 0 < M := by linarith
  have hRh : R ≤ r₀ n/2 := by linarith [le_trans (le_max_left (2*R) (2*M)) hrn]
  have hMd : M*d n ≤ r₀ n/2 := by nlinarith [le_trans (le_max_right (2*R) (2*M)) hrn]
  have he : (∫ t in R..(r₀ n-M*d n), (25/4 : ℝ)*
      ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
        ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖) =
      (25/4 : ℝ)*(∫ t in R..(r₀ n-M*d n),
        ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
          ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left (spectralTurning_outer_negative_error h (b n) (eta n)
    (omega n) (gamma n) (r₀ n) (d n) M R heta hrp hdp hMp hR hRh hMd hz hsc)
      (by norm_num : (0 : ℝ) ≤ 25/4)).trans hbn.le

end DefocusingNLS

end OAI
