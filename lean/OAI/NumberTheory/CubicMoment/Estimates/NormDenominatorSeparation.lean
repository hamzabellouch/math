import OAI.NumberTheory.CubicMoment.Estimates.NormDenominatorMellin

namespace OAI

/-! Exact separation of the square-root norm denominator in Poisson summation. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominator_radial_mellin_separated (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    (Real.exp ((Real.log x-Real.log y)/2):ℂ)*radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      normDenominatorMellinCoefficient M hM W hW hW' ρ t*gramMellinPhase t x*star (gramMellinPhase t y) := by
  have hk := normDenominatorLogSchwartz_eq_radial M hM W hW hW' hρ hxy
  rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hy,← mul_div_assoc] at hk
  rw [← hk]
  have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f (Real.log x-Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ,ℂ))
      (normDenominatorLogSchwartz M hM W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at he
  change normDenominatorLogSchwartz M hM W hW hW' ρ (Real.log x-Real.log y) = _
  rw [← he]
  apply integral_congr_ae
  filter_upwards with t
  have hi : inner ℝ t (Real.log x-Real.log y) = t*Real.log x-t*Real.log y := by
    simp only [RCLike.inner_apply,conj_trivial]
    ring
  have hp : (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ) =
      gramMellinPhase t x*star (gramMellinPhase t y) := by
    rw [hi,AddChar.map_sub_eq_div,div_eq_mul_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]
    rfl
  change (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ)*
    normDenominatorMellinCoefficient M hM W hW hW' ρ t = _
  rw [hp]
  ring

lemma exp_half_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp ((Real.log x-Real.log y)/2) = Real.sqrt x/Real.sqrt y := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hy,← Real.exp_sub]
  congr 1
  ring

theorem normDenominator_radial_div_sqrt (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    radialDualProfile W (ρ*x/y)/(Real.sqrt y:ℂ) = ∫ t : ℝ,
      (Real.sqrt x:ℂ)⁻¹*normDenominatorMellinCoefficient M hM W hW hW' ρ t*
        gramMellinPhase t x*star (gramMellinPhase t y) := by
  have he := normDenominator_radial_mellin_separated M hM W hW hW' hρ hx hy hxy
  rw [exp_half_log_ratio hx hy,Complex.ofReal_div] at he
  calc
    _ = (Real.sqrt x:ℂ)⁻¹ * ((Real.sqrt x:ℂ)/(Real.sqrt y:ℂ)*radialDualProfile W (ρ*x/y)) := by
      have hs : (Real.sqrt x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
      field_simp
    _ = _ := by
      rw [he,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring

end CubicFirstMoment

end

end OAI
