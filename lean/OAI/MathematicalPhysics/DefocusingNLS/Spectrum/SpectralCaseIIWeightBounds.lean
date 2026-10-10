import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIIShellFrequency
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! On a Case II shell the scalar momentum is comparable to sqrt(omega). -/

namespace DefocusingNLS

theorem spectralWKBSquaredMomentum_norm_upper (sign F gamma : ℝ)
    (hs : sign^2 = 1) : ‖spectralWKBSquaredMomentum sign F gamma‖ ≤ |F|+|gamma| := by
  have hsign : |sign| = 1 := by nlinarith [sq_abs sign,abs_nonneg sign]
  unfold spectralWKBSquaredMomentum
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hsign,one_mul]
  simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] using
    norm_add_le (F : ℂ) (Complex.I*(gamma : ℂ))

theorem spectralWKB_momentum_shell_bounds (sign F gamma omega A : ℝ)
    (hs : sign^2 = 1) (hw : 1 ≤ omega) (hA : 0 ≤ A)
    (hFlo : omega/2 ≤ |F|) (hFhi : |F| ≤ A*omega) (hg : |gamma| ≤ 8) :
    Real.sqrt omega/2 ≤ ‖Complex.sqrt (spectralWKBSquaredMomentum sign F gamma)‖ ∧
    ‖Complex.sqrt (spectralWKBSquaredMomentum sign F gamma)‖ ≤ (A+9)*Real.sqrt omega := by
  let p := Complex.sqrt (spectralWKBSquaredMomentum sign F gamma)
  have hn := spectralComplexSqrt_norm_sq (spectralWKBSquaredMomentum sign F gamma)
  have hlow := spectralWKBSquaredMomentum_norm_lower sign F gamma hs
  have hhigh := spectralWKBSquaredMomentum_norm_upper sign F gamma hs
  have hw0 : 0 ≤ omega := by linarith
  have hsqrt := Real.sq_sqrt hw0
  have hsqrtn := Real.sqrt_nonneg omega
  have hpn : 0 ≤ ‖p‖ := norm_nonneg _
  change Real.sqrt omega/2 ≤ ‖p‖ ∧ ‖p‖ ≤ (A+9)*Real.sqrt omega
  change ‖p‖^2 = _ at hn
  have hp2 : ‖p‖^2 ≤ (A+8)*omega := by
    have h8 := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith
  have hscale : A+8 ≤ (A+9)^2 := by nlinarith [sq_nonneg A]
  have hupper := mul_le_mul_of_nonneg_right hscale hw0
  constructor
  · nlinarith
  · by_contra hh
    have hgt : (A+9)*Real.sqrt omega < ‖p‖ := lt_of_not_ge hh
    have hpos : 0 ≤ (A+9)*Real.sqrt omega := by positivity
    nlinarith [(sq_lt_sq₀ hpos hpn).mpr hgt]

theorem spectralCaseII_momentum_bounds (b eta omega gamma C R B r : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (heta : 0 ≤ eta) (hC : 0 ≤ C)
    (hR : 0 < R) (hRr : R ≤ r) (hrB : r ≤ B)
    (hlarge : 2*(B^2/16+1) ≤ omega) (hL : eta+99/4 ≤ C*omega)
    (hCR : 2*C ≤ R^2) (hg : |gamma| ≤ 8) :
    (Real.sqrt omega/2 ≤ ‖spectralLiouvilleMomentum (-1) 1 b eta omega gamma r‖ ∧
      ‖spectralLiouvilleMomentum (-1) 1 b eta omega gamma r‖ ≤ (C/R^2+11)*Real.sqrt omega) ∧
    (Real.sqrt omega/2 ≤ ‖spectralLiouvilleMomentum 1 (-1) b eta omega (-gamma) r‖ ∧
      ‖spectralLiouvilleMomentum 1 (-1) b eta omega (-gamma) r‖ ≤ (C/R^2+11)*Real.sqrt omega) := by
  obtain ⟨hp,hm,hpa,hma⟩ := spectralCaseII_shell_frequency b eta omega C R B r
    hb hb1 heta hC hR hRr hrB hlarge hL hCR
  have hw : 1 ≤ omega := by nlinarith [sq_nonneg B]
  have hpl : omega/2 ≤ |homogeneousSpectralLocalizationFrequency 1 b eta omega r| := by
    exact le_trans (by linarith) (neg_le_abs _)
  have hml : omega/2 ≤ |homogeneousSpectralLocalizationFrequency (-1) b eta omega r| :=
    hm.trans (le_abs_self _)
  constructor
  · simpa only [spectralLiouvilleMomentum,show C/R^2+2+9 = C/R^2+11 by ring] using
      spectralWKB_momentum_shell_bounds (-1) _ gamma omega (C/R^2+2)
        (by norm_num) hw (by positivity) hpl hpa hg
  · simpa only [spectralLiouvilleMomentum,show C/R^2+2+9 = C/R^2+11 by ring] using
      spectralWKB_momentum_shell_bounds 1 _ (-gamma) omega (C/R^2+2)
        (by norm_num) hw (by positivity) hml hma (by simpa only [abs_neg] using hg)

end DefocusingNLS

end OAI
