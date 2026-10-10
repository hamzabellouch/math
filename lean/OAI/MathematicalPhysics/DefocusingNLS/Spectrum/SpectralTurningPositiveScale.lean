import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPositiveIntegral

namespace OAI

/-! A parameter-uniform near-turning error. The first term decays with the
fixed Airy cutoff and the second vanishes as the turning scale shrinks. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_positive_scaled_integral (h b eta omega r₀ d M c : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M)
    (hac : r₀+M*d≤c) (hc : c≤2*r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    (∫ t in (r₀+M*d)..c, (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
        (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t))^5+
      |spectralLiouvilleSecond eta t|/
        (4*(Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t))^3))≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8)) := by
  let a := r₀+M*d
  let p := Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega a)
  let s := Real.sqrt (M/8)
  let g := spectralLiouvilleSlope eta r₀
  have ha : r₀<a := by dsimp only [a]; nlinarith
  have har : a≤2*r₀ := hac.trans hc
  have hg : 0<g := by dsimp only [g,spectralLiouvilleSlope]; positivity
  have hgs : g*d^3=1 := hscale
  have hlow := (spectralTurningFrequency_growth h b eta omega r₀ a heta hr₀ ha.le har hz).1
  have hF : 0<homogeneousSpectralLocalizationFrequency h b eta omega a :=
    lt_of_lt_of_le (mul_pos (div_pos hg (by norm_num)) (sub_pos.2 ha)) hlow
  have hp : 0<p := Real.sqrt_pos.2 hF
  have hs : 0<s := Real.sqrt_pos.2 (by positivity)
  have hpsq : p^2=homogeneousSpectralLocalizationFrequency h b eta omega a := Real.sq_sqrt hF.le
  have hprod : s≤p*d := by
    apply Real.sqrt_le_iff.2
    refine ⟨mul_nonneg hp.le hd.le,?_⟩
    have hl := mul_le_mul_of_nonneg_right hlow (sq_nonneg d)
    have he : (g/8*(a-r₀))*d^2=M/8 := by
      dsimp only [a]
      calc
        _ = M/8*(g*d^3) := by ring
        _ = M/8 := by rw [hgs,mul_one]
    change (g/8*(a-r₀))*d^2≤_ at hl
    rw [he] at hl
    simpa only [mul_pow,hpsq] using hl
  have hcube := pow_le_pow_left₀ hs.le hprod 3
  have hgp : g*s^3≤p^3 := by
    calc
      _ ≤ g*(p*d)^3 := mul_le_mul_of_nonneg_left hcube hg.le
      _ = p^3*(g*d^3) := by ring
      _ = p^3 := by rw [hgs,mul_one]
  have h1 : g/p^3≤1/s^3 := (div_le_div_iff₀ (pow_pos hp 3) (pow_pos hs 3)).mpr (by simpa using hgp)
  have h2 : 1/p≤d/s := (div_le_div_iff₀ hp hs).mpr (by simpa only [one_mul,mul_comm d p] using hprod)
  have hb := spectralTurning_positive_integral h b eta omega r₀ a c heta hr₀ ha hac hc hz
  calc
    _ ≤ 5*(8*g)/(24*p^3)+(6/r₀)/(2*p) := hb
    _ = (5/3)*(g/p^3)+(3/r₀)*(1/p) := by ring
    _ ≤ (5/3)*(1/s^3)+(3/r₀)*(d/s) := add_le_add
      (mul_le_mul_of_nonneg_left h1 (by norm_num))
      (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by dsimp only [s]; ring

end DefocusingNLS

end OAI
