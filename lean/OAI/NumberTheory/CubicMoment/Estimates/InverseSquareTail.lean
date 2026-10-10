import OAI.NumberTheory.CubicMoment.Estimates.FourierTwoDerivatives

namespace OAI

/-! Integrability from the precise inverse-square tail used by far cells. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

theorem integrable_of_inverse_square_tail (f : ℝ → ℂ) (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (htail : ∀ x : ℝ, 2 ≤ |x| → ‖f x‖ ≤ C/x^2) :
    Integrable f := by
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn hf.continuousOn
  let M := 5*max B 0+2*C+1
  have hg : Integrable (fun x : ℝ => M/(1+x^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul M
  apply hg.mono' hf.aestronglyMeasurable
  filter_upwards with x
  apply (le_div_iff₀ (show 0 < 1+x^2 by positivity)).mpr
  by_cases hx : |x| ≤ 2
  · have hb : ‖f x‖ ≤ max B 0 := (hB x (abs_le.mp hx)).trans (le_max_left _ _)
    have hs : 1+x^2 ≤ 5 := by
      have hh := pow_le_pow_left₀ (abs_nonneg x) hx 2
      nlinarith only [hh,sq_abs x]
    have hm := mul_le_mul hb hs (by positivity : 0 ≤ 1+x^2) (le_max_right B 0)
    dsimp [M]
    linarith
  · have hx2 : 2 ≤ |x| := (lt_of_not_ge hx).le
    have hs : 1 ≤ x^2 := by nlinarith [sq_abs x]
    have hp : 0 < x^2 := by linarith
    have ht := (le_div_iff₀ hp).mp (htail x hx2)
    have hh : ‖f x‖ ≤ C := by nlinarith [_root_.norm_nonneg (f x)]
    dsimp [M]
    nlinarith [le_max_right B 0]

lemma norm_real_zpow_tail {x C : ℝ} (hx : 2 ≤ |x|) (hC : 0 ≤ C)
    {n : ℤ} (hn : n ≤ -2) : ‖(C*x^n : ℝ)‖ ≤ C/x^2 := by
  rw [norm_mul,Real.norm_of_nonneg hC,norm_zpow,Real.norm_eq_abs]
  have hp := zpow_le_zpow_right₀ (show 1 ≤ |x| by linarith) hn
  have he : |x|^(-2:ℤ) = (x^2)⁻¹ := by rw [zpow_neg,zpow_ofNat,sq_abs]
  rw [he] at hp
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp hC

end CubicFirstMoment

end

end OAI
