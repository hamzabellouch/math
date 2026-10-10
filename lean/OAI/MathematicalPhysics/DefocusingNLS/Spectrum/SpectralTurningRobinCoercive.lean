import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningActionGrowth

namespace OAI

/-! The fixed-shell growing cone gives a strictly inward logarithmic
slope for the scalar outgoing comparison. -/

namespace DefocusingNLS

theorem spectralRobin_ratio_coercive (p : ℂ) (u : ℂ × ℂ) (hu : u.1 ≠ 0)
    (hp : (2/3 : ℝ)*‖p‖ ≤ p.re)
    (hclose : ‖u.2+p*u.1‖ ≤ (5/8 : ℝ)*‖p‖*‖u.1‖) :
    (u.2/u.1).re ≤ -(1/24 : ℝ)*‖p‖ := by
  have hv : 0 < ‖u.1‖ := norm_pos_iff.mpr hu
  have he : u.2/u.1+p = (u.2+p*u.1)/u.1 := by field_simp
  have hn : ‖u.2/u.1+p‖ ≤ (5/8 : ℝ)*‖p‖ := by
    rw [he,norm_div]
    exact (div_le_iff₀ hv).mpr hclose
  have hr := (Complex.re_le_norm (u.2/u.1+p)).trans hn
  rw [Complex.add_re] at hr
  linarith

theorem spectralTurning_inner_robin_coercive (h b eta omega gamma r₀ R : ℝ)
    (heta : 0 ≤ eta) (hr₀ : 0 < r₀) (hR : 0 < R) (hRh : R ≤ r₀/2)
    (hlarge : 64 ≤ r₀*R)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀ = 0)
    (u : ℂ × ℂ) (hu : u.1 ≠ 0)
    (hcone :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma R
      ‖u.2+(p-(spectralLiouvilleSlope eta R : ℂ)/(4*p^2))*u.1‖ ≤
        (1/2 : ℝ)*‖p‖*‖u.1‖) :
    (u.2/u.1).re ≤ -(1/24 : ℝ)*‖spectralLiouvilleMomentum (-1) h b eta omega gamma R‖ := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega R
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma R
  let g := spectralLiouvilleSlope eta R
  obtain ⟨hFlo,hFg⟩ := spectralTurning_forbidden_far h b eta omega r₀ R heta hr₀ hR hRh hz
  have hFp : 0 < -F := by dsimp only [F]; nlinarith [sq_pos_of_pos hr₀]
  have he : spectralWKBSquaredMomentum (-1) F gamma = ((-F : ℝ) : ℂ)+Complex.I*((-gamma : ℝ) : ℂ) := by
    dsimp only [spectralWKBSquaredMomentum]
    push_cast
    ring
  have hre : (2/3 : ℝ)*‖p‖ ≤ p.re := by
    dsimp only [p,spectralLiouvilleMomentum]
    rw [he]
    exact spectralComplexSqrt_re_two_thirds (-F) (-gamma) hFp
  have hsq : ‖p‖^2 = ‖spectralWKBSquaredMomentum (-1) F gamma‖ := spectralComplexSqrt_norm_sq _
  have hnorm : -F ≤ ‖p‖^2 := (neg_le_abs F).trans (by
    rw [hsq]
    exact spectralWKBSquaredMomentum_norm_lower (-1) F gamma (by norm_num))
  have hplower : r₀/8 ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  have hpn : 0 < ‖p‖ := lt_of_lt_of_le (by positivity : 0 < r₀/8) hplower
  have hRp : 8 ≤ R*‖p‖ := by
    have hh := mul_le_mul_of_nonneg_left hplower hR.le
    nlinarith
  have hg : 0 ≤ g := by dsimp only [g,spectralLiouvilleSlope]; positivity
  have hgBound : g ≤ 4*‖p‖^2/R :=
    hFg.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num)) hR.le)
  have hc : ‖(g : ℂ)/(4*p^2)‖ ≤ ‖p‖/8 := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hg]
    norm_num only [Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0 < 4*‖p‖^2)).mpr
    have hgR := (le_div_iff₀ hR).mp hgBound
    have hmult := mul_le_mul_of_nonneg_left hRp (by positivity : 0 ≤ ‖p‖^2)
    nlinarith
  apply spectralRobin_ratio_coercive p u hu hre
  have hrep : u.2+p*u.1 = (u.2+(p-(g : ℂ)/(4*p^2))*u.1)+((g : ℂ)/(4*p^2))*u.1 := by ring
  rw [hrep]
  calc
    _ ≤ ‖u.2+(p-(g : ℂ)/(4*p^2))*u.1‖+‖((g : ℂ)/(4*p^2))*u.1‖ := norm_add_le _ _
    _ ≤ (1/2 : ℝ)*‖p‖*‖u.1‖+(‖p‖/8)*‖u.1‖ := by
      rw [norm_mul]
      exact add_le_add hcone (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    _ = _ := by ring

end DefocusingNLS

end OAI
