import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDerivativeTwist

namespace OAI

/-! Exact Mellin inversion of the actual character-twisted ideal von
Mangoldt sum, on its half-plane of absolute convergence. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def idealMangoldtSmooth (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' ν, (((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*W (idealExponentNorm ν/X)

theorem idealMangoldt_smooth_mellin
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X σ : ℝ} (hX : 0 < X) (hσ : 1 < σ) :
    idealMangoldtSmooth χ W X=((1/(2*Real.pi):ℝ):ℂ)*
      ∫ t : ℝ, mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)*(X:ℂ)^((σ:ℂ)+(t:ℂ)*Complex.I)*
        (-logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
  have habs : Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖*
      idealExponentNorm ν^(-σ)) := by
    have h := idealVonMangoldtDirichlet_norm_summable χ hχ
      (s := (σ:ℂ)) (by simpa using hσ)
    simpa only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos _),
      Complex.neg_re,Complex.ofReal_re] using h
  rw [idealMangoldtSmooth,smooth_mellin_series _ _ idealExponentNorm_pos W hW hpos hsm σ habs hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  have hst : 1 < ((σ:ℂ)+(t:ℂ)*Complex.I).re := by simpa using hσ
  rw [idealSeries_logDeriv_eq hs hst,idealDirichlet_neg_logDeriv χ hχ hχ0 hχadd hst]

end CubicFirstMoment

end

end OAI
