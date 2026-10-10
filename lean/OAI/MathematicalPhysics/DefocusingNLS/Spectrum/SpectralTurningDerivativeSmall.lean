import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidual

namespace OAI

/-! The cutoff M ≥ 32 makes the momentum derivative small on both near-turning
outer intervals. No solution estimate is assumed. -/

namespace DefocusingNLS

theorem spectralWKB_scaled_slope_small (d M p g : ℝ)
    (hd : 0<d) (hp : 0<p) (hg : 0≤g) (hM : 32≤M)
    (hscale : g*d^3=1) (hlow : (g/8)*(M*d)≤p^2) :
    8*g≤p^3 := by
  have hm := mul_le_mul_of_nonneg_left hM (show 0≤g*d/8 by positivity)
  have hl : 4*g*d≤p^2 := by nlinarith
  have hpd2 : 4≤(p*d)^2 := by
    have hh := mul_le_mul_of_nonneg_right hl (sq_nonneg d)
    calc
      _ = 4*(g*d^3) := by rw [hscale]; norm_num
      _ ≤ p^2*d^2 := by nlinarith [hh]
      _ = (p*d)^2 := (mul_pow p d 2).symm
  have hpd : 2≤p*d := by nlinarith [mul_pos hp hd]
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) hpd 3
  calc
    _ ≤ g*(p*d)^3 := by nlinarith [mul_le_mul_of_nonneg_left hcube hg]
    _ = p^3*(g*d^3) := by ring
    _ = p^3 := by rw [hscale,mul_one]

theorem spectralTurning_near_derivative_small
    (sign h b eta omega gamma r₀ d M r : ℝ)
    (hs : sign^2=1) (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 32≤M)
    (hr : r₀/2≤r) (hr' : r≤2*r₀) (hdist : M*d≤|r-r₀|)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    |spectralLiouvilleSlope eta r|≤
      2*‖spectralLiouvilleMomentum sign h b eta omega gamma r‖^3 := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega r
  let g := spectralLiouvilleSlope eta r₀
  let p := ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖
  have hrp : 0<r := by linarith
  have hg : 0<g := by dsimp only [g,spectralLiouvilleSlope]; positivity
  have hMd : 0<M*d := mul_pos (by linarith) hd
  have hlowF : (g/8)*(M*d)≤|F| := by
    rcases le_total r₀ r with hrr | hrr
    · have hh := (spectralTurningFrequency_growth h b eta omega r₀ r heta hr₀ hrr hr' hz).1
      have hdist' : M*d≤r-r₀ := by simpa only [abs_of_nonneg (sub_nonneg.2 hrr)] using hdist
      exact (mul_le_mul_of_nonneg_left hdist' (by positivity)).trans (hh.trans (le_abs_self _))
    · have hh := (spectralTurning_forbidden_growth h b eta omega r₀ r heta hr₀ hr hrr hz).1
      have hdist' : M*d≤r₀-r := by
        have he : |r-r₀|=r₀-r := by rw [abs_of_nonpos (sub_nonpos.2 hrr)]; ring
        simpa only [he] using hdist
      exact (mul_le_mul_of_nonneg_left hdist' (by positivity)).trans (hh.trans (neg_le_abs _))
  have hn : p^2=‖spectralWKBSquaredMomentum sign F gamma‖ := spectralComplexSqrt_norm_sq _
  have hlow : (g/8)*(M*d)≤p^2 := hlowF.trans (by
    rw [hn]
    exact spectralWKBSquaredMomentum_norm_lower sign F gamma hs)
  have hp : 0<p := by
    have hpos : 0<(g/8)*(M*d) := mul_pos (div_pos hg (by norm_num)) hMd
    have hn0 : 0≤p := norm_nonneg _
    nlinarith
  have hsmall := spectralWKB_scaled_slope_small d M p g hd hp hg.le hM hscale hlow
  have hgr : 0≤ spectralLiouvilleSlope eta r := by dsimp only [spectralLiouvilleSlope]; positivity
  have hnear := (spectralLiouvilleSlope_near eta r₀ r heta hr₀ hr hr').2
  rw [abs_of_nonneg hgr]
  exact hnear.trans (hsmall.trans (by nlinarith [pow_nonneg hp.le 3]))

end DefocusingNLS

end OAI
