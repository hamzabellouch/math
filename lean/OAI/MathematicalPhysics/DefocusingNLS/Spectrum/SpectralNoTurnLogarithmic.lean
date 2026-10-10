import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnValue
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLogarithmicRatio

namespace OAI

/-! The no-turn logarithmic slope approaches the negative imaginary branch,
with an explicit error that vanishes with the spectral parameter. -/

open Set
namespace DefocusingNLS

theorem spectralNoTurn_outgoing_logarithmic_bound
    (b eta omega gamma C R E : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (hC : 0 ≤ C) (hCw : C ≤ omega)
    (hR : 0 < R) (hRE : R ≤ E) (hE : 0 < E) (hEs : E^2 = 256*omega)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2)
    (hgamma : |gamma| ≤ 8) (hEbound : E ≤ 32*Real.sqrt (omega/2))
    (hlarge : 2/R+4*C/R^3 ≤ 2*Real.sqrt (omega/2))
    (hgF : |gamma| ≤ homogeneousSpectralLocalizationFrequency (-1) b eta omega E)
    (herrSmall : spectralNoTurnBranchError C R omega E ≤ Real.exp (-256)/2)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hqE : q E = spectralOscillatoryData (-1)
      (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E))))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency (-1) b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum 1 (-1) b eta omega gamma R
    (q R).1 ≠ 0 ∧ ‖((q R).2/(q R).1)/p+Complex.I‖ ≤
      5*spectralNoTurnBranchError C R omega E/Real.exp (-256)+
        (2/R+4*C/R^3)/(4*‖p‖) := by
  let p := spectralLiouvilleMomentum 1 (-1) b eta omega gamma R
  let K := 2/R+4*C/R^3
  let eps := 5*spectralNoTurnBranchError C R omega E/Real.exp (-256)
  obtain ⟨_hval,hq0,hlog⟩ := spectralNoTurn_outgoing_value b eta omega gamma C R E hb heta hw hC hCw
    hR hRE hE hEs hL hCR hgamma hEbound hlarge hgF herrSmall q hq hqE hODE
  have hFlo := spectralNoTurn_frequency_lower b eta omega C R R hb hw hR le_rfl hL hCR
  have hF : 0 < homogeneousSpectralLocalizationFrequency (-1) b eta omega R :=
    lt_of_lt_of_le (by positivity) hFlo
  have hp0 : p ≠ 0 := norm_pos_iff.mp
    ((Real.sqrt_pos.mpr (by positivity : 0 < omega/2)).trans_le
      (spectralNoTurn_momentum_lower b eta omega gamma C R R hb hw hR le_rfl hL hCR))
  have hnorm : homogeneousSpectralLocalizationFrequency (-1) b eta omega R ≤ ‖p‖^2 := by
    have hl := spectralWKBSquaredMomentum_norm_lower 1
      (homogeneousSpectralLocalizationFrequency (-1) b eta omega R) gamma (by norm_num)
    have he := spectralComplexSqrt_norm_sq
      (spectralWKBSquaredMomentum 1 (homogeneousSpectralLocalizationFrequency (-1) b eta omega R) gamma)
    exact (le_abs_self _).trans (hl.trans_eq he.symm)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hg : ‖(spectralLiouvilleSlope eta R : ℂ)‖ ≤ K*‖p‖^2 := by
    have hg0 : 0 ≤ spectralLiouvilleSlope eta R := by dsimp only [spectralLiouvilleSlope]; positivity
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hg0]
    exact (spectralNoTurn_slope_bound b eta omega C R R hb heta hw hC hR le_rfl hL hCR).trans
      (mul_le_mul_of_nonneg_left hnorm hK)
  have heq : homogeneousSpectralWKBLog (-Complex.I) p ((spectralLiouvilleSlope eta R : ℂ)/(2*p)) =
      (-Complex.I)*p-(spectralLiouvilleSlope eta R : ℂ)/(4*p^2) := by
    dsimp only [homogeneousSpectralWKBLog]
    field_simp
    ring
  change ‖(q R).2/(q R).1-homogeneousSpectralWKBLog (-Complex.I) p
    ((spectralLiouvilleSlope eta R : ℂ)/(2*p))‖ ≤ eps*‖p‖ at hlog
  rw [heq] at hlog
  have hh := spectralLogarithmicRatio_bound p ((q R).2/(q R).1)
    (spectralLiouvilleSlope eta R : ℂ) (-Complex.I) eps K hp0 hK hlog hg
  exact ⟨hq0,by simpa only [sub_neg_eq_add] using hh⟩

end DefocusingNLS

end OAI
