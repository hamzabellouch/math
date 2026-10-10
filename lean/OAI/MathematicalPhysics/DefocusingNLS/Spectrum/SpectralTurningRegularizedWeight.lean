import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaledNorm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! A continuous positive frequency weight agrees with the WKB weight away
from the turn and remains nondegenerate on the scaled central interval. -/

open Set
namespace DefocusingNLS

theorem spectralComplexSqrt_norm (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  have hs := spectralComplexSqrt_norm_sq z
  have hr := Real.sq_sqrt (norm_nonneg z)
  nlinarith [norm_nonneg (Complex.sqrt z),Real.sqrt_nonneg ‖z‖]

noncomputable def spectralTurningRegularizedWeight (h b eta omega gamma d r : ℝ) : ℝ :=
  max (Real.sqrt d)⁻¹ (Real.sqrt (Real.sqrt
    ‖(homogeneousSpectralLocalizationFrequency h b eta omega r : ℂ)+Complex.I*(gamma : ℂ)‖))

theorem spectralTurningRegularizedWeight_pos (h b eta omega gamma d r : ℝ) (hd : 0 < d) :
    0 < spectralTurningRegularizedWeight h b eta omega gamma d r :=
  lt_of_lt_of_le (inv_pos.mpr (Real.sqrt_pos.mpr hd)) (le_max_left _ _)

theorem spectralTurningRegularizedWeight_continuousOn (h b eta omega gamma d : ℝ) :
    ContinuousOn (spectralTurningRegularizedWeight h b eta omega gamma d) (Ioi 0) := by
  have hF : ContinuousOn (homogeneousSpectralLocalizationFrequency h b eta omega) (Ioi 0) :=
    fun r hr => (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega r hr).continuousAt.continuousWithinAt
  exact continuousOn_const.sup (Real.continuous_sqrt.comp_continuousOn
    (Real.continuous_sqrt.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hF).add continuousOn_const).norm))

theorem spectralTurningRegularizedWeight_eq_wkb (h b eta omega gamma d r : ℝ)
    (hweight : (Real.sqrt d)⁻¹ ≤
      Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖) :
    spectralTurningRegularizedWeight h b eta omega gamma d r =
      Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖ := by
  have he : Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖ =
      Real.sqrt (Real.sqrt ‖(homogeneousSpectralLocalizationFrequency h b eta omega r : ℂ)+
        Complex.I*(gamma : ℂ)‖) := by
    simp only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
      one_mul,spectralComplexSqrt_norm]
  rw [he] at hweight ⊢
  exact max_eq_right hweight

theorem spectralTurningRegularizedWeight_scaled (h b eta omega gamma r₀ d xi : ℝ) (hd : 0 < d) :
    Real.sqrt d*spectralTurningRegularizedWeight h b eta omega gamma d (r₀+d*xi) =
      max 1 (Real.sqrt (Real.sqrt ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [spectralTurningRegularizedWeight,mul_max_of_nonneg _ _ hs.le,mul_inv_cancel₀ hs.ne']
  congr 1
  simpa only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
    one_mul,spectralComplexSqrt_norm] using
    spectralTurning_scaled_weight h b eta omega gamma r₀ d xi hd.le


theorem spectralTurningRegularizedWeight_eq_of_frequency
    (h b eta omega gamma d r : ℝ) (hd : 0 < d)
    (hlarge : 1 ≤ d^2*|homogeneousSpectralLocalizationFrequency h b eta omega r|) :
    spectralTurningRegularizedWeight h b eta omega gamma d r =
      Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖ := by
  let z : ℂ := (homogeneousSpectralLocalizationFrequency h b eta omega r : ℂ)+Complex.I*(gamma : ℂ)
  have hz : |homogeneousSpectralLocalizationFrequency h b eta omega r| ≤ ‖z‖ := by
    simpa only [z,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul] using
      spectralWKBSquaredMomentum_norm_lower 1 (homogeneousSpectralLocalizationFrequency h b eta omega r) gamma (by norm_num)
  have hn : 1 ≤ ‖(d : ℂ)^2*z‖ := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    exact hlarge.trans (mul_le_mul_of_nonneg_left hz (sq_nonneg d))
  have hs : 1 ≤ Real.sqrt d*Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖ := by
    have he := spectralComplexSqrt_scaled_weight d hd.le z
    have hroot := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hn)
    simpa only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul,z,← he] using hroot
  apply spectralTurningRegularizedWeight_eq_wkb
  exact (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hd)).mpr (by simpa only [mul_comm] using hs)


theorem spectralTurningRegularizedWeight_scaled_bounds (h b eta omega gamma r₀ d xi M : ℝ)
    (hd : 0 < d) (hM : 0 ≤ M)
    (hcoef : ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖ ≤ M+1) :
    1 ≤ Real.sqrt d*spectralTurningRegularizedWeight h b eta omega gamma d (r₀+d*xi) ∧
      Real.sqrt d*spectralTurningRegularizedWeight h b eta omega gamma d (r₀+d*xi) ≤ M+3 := by
  rw [spectralTurningRegularizedWeight_scaled h b eta omega gamma r₀ d xi hd]
  refine ⟨le_max_left _ _,max_le (by linarith) ?_⟩
  have hsqrt (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ x+1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg x]
  exact (hsqrt _ (Real.sqrt_nonneg _)).trans
    ((add_le_add (hsqrt _ (norm_nonneg _)) (le_refl (1 : ℝ))).trans (by linarith))


theorem spectralLiouville_weight_sign (sign h b eta omega gamma r : ℝ) (hs : sign^2 = 1) :
    Real.sqrt ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖ =
      Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma r‖ := by
  have habs : |sign| = 1 := by nlinarith [sq_abs sign,abs_nonneg sign]
  simp only [spectralLiouvilleMomentum,spectralComplexSqrt_norm,spectralWKBSquaredMomentum,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,habs,Complex.ofReal_one,one_mul]

end DefocusingNLS

end OAI
