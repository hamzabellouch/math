import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair

namespace OAI

/-! The Liouville Cauchy data on a fixed shell are bounded by the physical
radial H¹ density, with a constant independent of the spectral parameters. -/

namespace DefocusingNLS

theorem spectralLiouvilleFactor_norm_sq (h r : ℝ) (hr : 0 < r) :
    ‖homogeneousSpectralLocalizationFactor h r‖^2 = r^11 := by
  rw [homogeneousSpectralLocalizationFactor_norm h r hr,← Real.rpow_mul_natCast hr.le]
  norm_num

theorem spectralLiouvilleSlope_shell_bound (h R B r : ℝ)
    (hh : |h| ≤ 1) (hR : 0 < R) (hRr : R ≤ r) (hrB : r ≤ B) :
    ‖homogeneousSpectralLocalizationSlope h r‖ ≤ 11/(2*R)+B/4 := by
  have hr : 0 < r := hR.trans_le hRr
  have he := norm_add_le (11/(2*(r : ℂ))) ((h : ℂ)*Complex.I*(r : ℂ)/4)
  change ‖homogeneousSpectralLocalizationSlope h r‖ ≤ _ at he
  have hn : ‖(11/(2*(r : ℂ)) : ℂ)‖ = 11/(2*r) := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    norm_num
  have hn' : ‖((h : ℂ)*Complex.I*(r : ℂ)/4 : ℂ)‖ = |h| *r/4 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    norm_num
  rw [hn,hn'] at he
  apply he.trans
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (mul_le_mul_of_nonneg_right hh hr.le).trans (by simpa only [one_mul] using hrB)

theorem spectralLiouvilleState_slope_energy (h R B r : ℝ)
    (hh : |h| ≤ 1) (hR : 0 < R) (hRr : R ≤ r) (hrB : r ≤ B)
    (u v : ℂ) :
    ‖homogeneousSpectralLocalizationFactor h r*(v+homogeneousSpectralLocalizationSlope h r*u)‖^2 ≤
      2*r^11*(‖v‖^2+(11/(2*R)+B/4)^2*‖u‖^2) := by
  let S := 11/(2*R)+B/4
  have hr : 0 < r := hR.trans_le hRr
  have hB : 0 < B := hr.trans_le hrB
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hs := spectralLiouvilleSlope_shell_bound h R B r hh hR hRr hrB
  have hmul : ‖homogeneousSpectralLocalizationSlope h r*u‖ ≤ S*‖u‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  have hsum : ‖v+homogeneousSpectralLocalizationSlope h r*u‖ ≤ ‖v‖+S*‖u‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl hmul)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  have he : ‖v+homogeneousSpectralLocalizationSlope h r*u‖^2 ≤
      2*(‖v‖^2+S^2*‖u‖^2) := by
    nlinarith [sq_nonneg (‖v‖-S*‖u‖)]
  rw [norm_mul,mul_pow,spectralLiouvilleFactor_norm_sq h r hr]
  have hm := mul_le_mul_of_nonneg_left he (pow_nonneg hr.le 11)
  convert hm using 1
  ring

end DefocusingNLS

end OAI
