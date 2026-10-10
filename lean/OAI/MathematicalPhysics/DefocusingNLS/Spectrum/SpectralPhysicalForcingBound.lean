import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalShellEnergy

namespace OAI

/-! Bound the actual scalar forcing by the physical shell mass. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralPhysicalLiouvillePair_value_sq (f g : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    ‖(spectralPhysicalLiouvillePair f g r).1.1‖^2 = r^11*‖f r‖^2 ∧
    ‖(spectralPhysicalLiouvillePair f g r).2.1‖^2 = r^11*‖g r‖^2 := by
  constructor <;> simp only [spectralPhysicalLiouvillePair,homogeneousSpectralLocalizationState,
    norm_mul,mul_pow,spectralLiouvilleFactor_norm_sq _ r hr]

theorem spectralPhysicalLiouvillePair_minus_forcing_sq
    (R r : ℝ) (hR : 0 < R) (hRr : R ≤ r) (m : ℕ) (Q : ℂ) (f g : ℝ → ℂ)
    (hc : ‖spectralDiagonalCoefficient m Q‖+‖spectralCrossCoefficient m Q‖ ≤ 1/r^2) :
    ‖spectralShellMinusForcing m Q r (spectralPhysicalLiouvillePair f g r)‖^2 ≤
      (1/R^2)^2*spectralPhysicalShellDensity f g r := by
  let q := spectralPhysicalLiouvillePair f g r
  have hr : 0 < r := hR.trans_le hRr
  have hb := homogeneousSpectralLocalization_coupling_bound (-1) r hr
    (star (spectralDiagonalCoefficient m Q)) (star (spectralCrossCoefficient m Q)) q.2.1 q.1.1
  simp only [norm_star,neg_neg] at hb
  change ‖spectralShellMinusForcing m Q r q‖ ≤ _ at hb
  have hd : 1/r^2 ≤ 1/R^2 := div_le_div_of_nonneg_left (by norm_num)
    (sq_pos_of_pos hR) (pow_le_pow_left₀ hR.le hRr 2)
  have hb' : ‖spectralShellMinusForcing m Q r q‖ ≤ (1/R^2)*max ‖q.2.1‖ ‖q.1.1‖ :=
    hb.trans (mul_le_mul_of_nonneg_right (hc.trans hd) (le_max_of_le_left (norm_nonneg _)))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb' 2
  have hm : (max ‖q.2.1‖ ‖q.1.1‖)^2 ≤ ‖q.1.1‖^2+‖q.2.1‖^2 := by
    rcases le_total ‖q.2.1‖ ‖q.1.1‖ with hh | hh
    · rw [max_eq_right hh]
      nlinarith [sq_nonneg ‖q.2.1‖]
    · rw [max_eq_left hh]
      nlinarith [sq_nonneg ‖q.1.1‖]
  have hv := spectralPhysicalLiouvillePair_value_sq f g r hr
  have hbd := mul_le_mul_of_nonneg_left hm (sq_nonneg (1/R^2))
  change ‖q.1.1‖^2 = _ ∧ ‖q.2.1‖^2 = _ at hv
  rw [hv.1,hv.2] at hbd
  have hmass : r^11*‖f r‖^2+r^11*‖g r‖^2 ≤ spectralPhysicalShellDensity f g r := by
    dsimp only [spectralPhysicalShellDensity]
    nlinarith [mul_nonneg (pow_nonneg hr.le 11) (sq_nonneg ‖deriv f r‖),
      mul_nonneg (pow_nonneg hr.le 11) (sq_nonneg ‖deriv g r‖)]
  exact (hs.trans_eq (mul_pow _ _ 2)).trans (hbd.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)))

end DefocusingNLS

end OAI
