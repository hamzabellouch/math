import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleRelativeResidual
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! The full no-turn residual tends to zero in the frequency-dominated case. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralNoTurn_residual_integral (b eta omega gamma C R E : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (hC : 0 ≤ C)
    (hR : 0 < R) (hRE : R ≤ E) (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2) :
    (∫ t in R..E, ‖spectralLiouvilleResidual 1 (-1) b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum 1 (-1) b eta omega gamma t‖) ≤
        2*((5/16)*(2/R+4*C/R^3)+3/(4*R))/Real.sqrt (omega/2) := by
  have hF (t : ℝ) (ht : t ∈ Icc R E) :
      0 < homogeneousSpectralLocalizationFrequency (-1) b eta omega t :=
    lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower b eta omega C R t hb hw hR ht.1 hL hCR)
  have hj := spectralLiouville_relative_residual_integral (-1) b eta omega gamma R E
    (2/R+4*C/R^3) hR hRE heta (by positivity) hF
    (fun t ht => spectralNoTurn_slope_bound b eta omega C R t hb heta hw hC hR ht.1 hL hCR)
  apply hj.trans
  apply div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by positivity))
  apply Real.sqrt_le_sqrt
  have hlo := spectralNoTurn_frequency_lower b eta omega C R R hb hw hR le_rfl hL hCR
  nlinarith [sq_nonneg R]

theorem spectralNoTurn_residual_tendsto (b eta omega gamma E : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ 0 ≤ eta n ∧ R ≤ E n ∧ eta n+99/4 ≤ C*omega n) :
    Tendsto (fun n => ∫ t in R..E n,
      ‖spectralLiouvilleResidual 1 (-1) (b n) (eta n) (omega n) (gamma n) t‖/
        ‖spectralLiouvilleMomentum 1 (-1) (b n) (eta n) (omega n) (gamma n) t‖) atTop (𝓝 0) := by
  have hroot : Tendsto (fun n => Real.sqrt (omega n/2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hw.atTop_div_const (by norm_num))
  have hbound := (tendsto_inv_atTop_zero.comp hroot).const_mul
    (2*((5/16 : ℝ)*(2/R+4*C/R^3)+3/(4*R)))
  have hbound' : Tendsto (fun n =>
      2*((5/16 : ℝ)*(2/R+4*C/R^3)+3/(4*R))/Real.sqrt (omega n/2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using hbound
  apply squeeze_zero' _ _ hbound'
  · filter_upwards [hdata] with n hn
    exact intervalIntegral.integral_nonneg hn.2.2.1 (fun t _ => by positivity)
  · filter_upwards [hdata,hw.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hwn
    exact spectralNoTurn_residual_integral (b n) (eta n) (omega n) (gamma n) C R (E n)
      hn.1 hn.2.1 hwn hC hR hn.2.2.1 hn.2.2.2 hCR

end DefocusingNLS

end OAI
