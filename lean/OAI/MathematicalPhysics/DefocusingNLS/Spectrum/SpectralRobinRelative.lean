import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRobinCoercive

namespace OAI

/-! Relative Robin errors separate into the propagated cone error and the
explicit logarithmic derivative of the WKB amplitude. -/

namespace DefocusingNLS

theorem spectralRobin_relative_residual (p c : ℂ) (u : ℂ × ℂ) (eps : ℝ)
    (hu : u.1 ≠ 0) (hp : p ≠ 0)
    (hclose : ‖u.2+(p-c)*u.1‖ ≤ eps*‖p‖*‖u.1‖) :
    ‖u.2/u.1/p+1‖ ≤ eps+‖c/p‖ := by
  have he : u.2/u.1/p+1 = (u.2+(p-c)*u.1)/(u.1*p)+c/p := by
    field_simp
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  refine add_le_add ?_ le_rfl
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hp))).mpr
  calc
    _ ≤ eps*‖p‖*‖u.1‖ := hclose
    _ = _ := by ring

theorem spectralTurning_log_correction_bound (h b eta omega gamma r₀ R : ℝ)
    (heta : 0 ≤ eta) (hr₀ : 0 < r₀) (hR : 0 < R) (hRh : R ≤ r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀ = 0) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma R
    ‖((spectralLiouvilleSlope eta R : ℂ)/(4*p^2))/p‖ ≤ 16/(R*r₀) := by
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma R
  let g := spectralLiouvilleSlope eta R
  have hpre := spectralTurning_far_momentum_re_lower h b eta omega gamma r₀ R heta hr₀ hR hRh hz
  have hpl : r₀/16 ≤ ‖p‖ := hpre.trans (Complex.re_le_norm p)
  have hpn : 0 < ‖p‖ := lt_of_lt_of_le (by positivity) hpl
  have hg : 0 ≤ g := by dsimp only [g,spectralLiouvilleSlope]; positivity
  have hfar := (spectralTurning_forbidden_far h b eta omega r₀ R heta hr₀ hR hRh hz).2
  have hnorm : -homogeneousSpectralLocalizationFrequency h b eta omega R ≤ ‖p‖^2 := by
    have he : ‖p‖^2 = ‖spectralWKBSquaredMomentum (-1)
        (homogeneousSpectralLocalizationFrequency h b eta omega R) gamma‖ := spectralComplexSqrt_norm_sq _
    exact (neg_le_abs _).trans (he.symm ▸
      spectralWKBSquaredMomentum_norm_lower (-1) _ gamma (by norm_num))
  have hgBound : g ≤ 4*‖p‖^2/R := hfar.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num)) hR.le)
  have hEq : ‖((g : ℂ)/(4*p^2))/p‖ = g/(4*‖p‖^3) := by
    rw [norm_div,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hg]
    norm_num only [Complex.norm_ofNat]
    ring
  change ‖((g : ℂ)/(4*p^2))/p‖ ≤ _
  rw [hEq]
  apply (div_le_div_iff₀ (by positivity : 0 < 4*‖p‖^3) (mul_pos hR hr₀)).mpr
  have hgR := (le_div_iff₀ hR).mp hgBound
  have h₁ := mul_le_mul_of_nonneg_right hgR hr₀.le
  have h₂ := mul_le_mul_of_nonneg_left hpl (by positivity : 0 ≤ 64*‖p‖^2)
  nlinarith

end DefocusingNLS

end OAI
