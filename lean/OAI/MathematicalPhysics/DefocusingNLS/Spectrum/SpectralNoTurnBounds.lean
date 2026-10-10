import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleNormPositive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The no-turn momentum has a uniform lower bound, a bounded phase
integral, and the small derivative needed by the scalar WKB theorem. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralNoTurn_momentum_lower (b eta omega gamma C R r : ℝ)
    (hb : 0 ≤ b) (hw : 0 < omega) (hR : 0 < R) (hr : R ≤ r)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2) :
    Real.sqrt (omega/2) ≤ ‖spectralLiouvilleMomentum 1 (-1) b eta omega gamma r‖ := by
  have hf := spectralNoTurn_frequency_lower b eta omega C R r hb hw hR hr hL hCR
  have hFp : 0 < homogeneousSpectralLocalizationFrequency (-1) b eta omega r :=
    lt_of_lt_of_le (by positivity) hf
  calc
    _ ≤ Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega r) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])
    _ = Real.sqrt |homogeneousSpectralLocalizationFrequency (-1) b eta omega r| := by rw [abs_of_pos hFp]
    _ ≤ _ := spectralWKBSqrt_frequency_lower 1 _ gamma (by norm_num)

theorem spectralNoTurn_derivative_small (b eta omega gamma C R r : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (hC : 0 ≤ C)
    (hR : 0 < R) (hr : R ≤ r) (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2)
    (hlarge : 2/R+4*C/R^3 ≤ 2*Real.sqrt (omega/2)) :
    |spectralLiouvilleSlope eta r| ≤ 2*‖spectralLiouvilleMomentum 1 (-1) b eta omega gamma r‖^3 := by
  let p := ‖spectralLiouvilleMomentum 1 (-1) b eta omega gamma r‖
  let K := 2/R+4*C/R^3
  have hp : Real.sqrt (omega/2) ≤ p := spectralNoTurn_momentum_lower b eta omega gamma C R r hb hw hR hr hL hCR
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hnorm : homogeneousSpectralLocalizationFrequency (-1) b eta omega r ≤ p^2 := by
    have hl := spectralWKBSquaredMomentum_norm_lower 1
      (homogeneousSpectralLocalizationFrequency (-1) b eta omega r) gamma (by norm_num)
    have he := spectralComplexSqrt_norm_sq
      (spectralWKBSquaredMomentum 1 (homogeneousSpectralLocalizationFrequency (-1) b eta omega r) gamma)
    exact (le_abs_self _).trans (hl.trans_eq he.symm)
  have hg := (spectralNoTurn_slope_bound b eta omega C R r hb heta hw hC hR hr hL hCR).trans
    (mul_le_mul_of_nonneg_left hnorm hK)
  have hgp : K ≤ 2*p := hlarge.trans (by linarith)
  have ht := mul_le_mul_of_nonneg_right hgp (sq_nonneg p)
  have hg0 : 0 ≤ spectralLiouvilleSlope eta r := by
    have hr0 := hR.trans_le hr
    dsimp only [spectralLiouvilleSlope]
    positivity
  rw [abs_of_nonneg hg0]
  nlinarith

theorem spectralNoTurn_phase_bound (b eta omega C R E P : ℝ)
    (hb : 0 ≤ b) (hw : 0 < omega) (hR : 0 < R) (hRE : R ≤ E)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2)
    (hE : E ≤ P*Real.sqrt (omega/2)) :
    (∫ t in R..E, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega t)) ≤ P := by
  have hF (t : ℝ) (ht : t ∈ Icc R E) : 0 < homogeneousSpectralLocalizationFrequency (-1) b eta omega t :=
    lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower b eta omega C R t hb hw hR ht.1 hL hCR)
  have hfc : ContinuousOn (fun t => 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency (-1) b eta omega t)) (Icc R E) :=
    continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt (-1) b eta omega t
        (hR.trans_le ht.1)).continuousAt.continuousWithinAt))
      (fun t ht => (Real.sqrt_pos.mpr (hF t ht)).ne')
  have hp : 0 < Real.sqrt (omega/2) := Real.sqrt_pos.mpr (by positivity)
  have hi := intervalIntegral.integral_mono_on hRE (hfc.intervalIntegrable_of_Icc hRE)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1/Real.sqrt (omega/2)) volume R E)
    (fun t ht => one_div_le_one_div_of_le hp (Real.sqrt_le_sqrt (by
      have hh := spectralNoTurn_frequency_lower b eta omega C R t hb hw hR ht.1 hL hCR
      nlinarith [sq_nonneg t])))
  rw [intervalIntegral.integral_const] at hi
  change (∫ t in R..E, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega t)) ≤ P
  apply hi.trans
  change (E-R)*(1/Real.sqrt (omega/2)) ≤ P
  calc
    (E-R)*(1/Real.sqrt (omega/2)) = (E-R)/Real.sqrt (omega/2) := by ring
    _ ≤ P := (div_le_iff₀ hp).mpr (by linarith)

end DefocusingNLS

end OAI
