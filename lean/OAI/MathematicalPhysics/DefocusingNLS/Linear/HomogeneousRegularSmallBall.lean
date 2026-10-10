import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularZero

namespace OAI

/-! A local Dirichlet uniqueness estimate for the two radial channels. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousRegular_pair_zero_of_bound (R eta C : ℝ)
    (hR : 0 < R) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hsmall : C * R ^ 2 < 8)
    (F G H J : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (hH : Continuous H) (hJ : Continuous J) (hFR : F R = 0) (hGR : G R = 0)
    (hODEF : ∀ r, 0 < r → r ≤ R → deriv (deriv F) r +
      ((11 / r : ℝ) : ℂ) * deriv F r - ((eta / r ^ 2 : ℝ) : ℂ) * F r = H r)
    (hODEG : ∀ r, 0 < r → r ≤ R → deriv (deriv G) r +
      ((11 / r : ℝ) : ℂ) * deriv G r - ((eta / r ^ 2 : ℝ) : ℂ) * G r = J r)
    (hbound : ∀ r ∈ Icc 0 R,
      -((star (F r) * H r).re + (star (G r) * J r).re) ≤
        C * (‖F r‖ ^ 2 + ‖G r‖ ^ 2) + (‖deriv F r‖ ^ 2 + ‖deriv G r‖ ^ 2) / 2) :
    ∀ r ∈ Icc 0 R, F r = 0 ∧ G r = 0 := by
  let I := (∫ r in (0 : ℝ)..R, r ^ 11 * ‖F r‖ ^ 2) +
    (∫ r in (0 : ℝ)..R, r ^ 11 * ‖G r‖ ^ 2)
  let E := (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv F r‖ ^ 2) +
    (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv G r‖ ^ 2)
  have hEF := homogeneousRegular_complex_energy R eta hR.le F H hF hH hFR hODEF
  have hEG := homogeneousRegular_complex_energy R eta hR.le G J hG hJ hGR hODEG
  have hPF := homogeneousRegular_complex_poincare R hR.le F (hF.of_le (by norm_num)) hFR
  have hPG := homogeneousRegular_complex_poincare R hR.le G (hG.of_le (by norm_num)) hGR
  have hPN : 16 * I ≤ R ^ 2 * E := by dsimp only [I, E]; nlinarith [hPF, hPG]
  have hnon (k : ℕ) (f : ℝ → ℂ) :
      0 ≤ ∫ r in (0 : ℝ)..R, r ^ k * ‖f r‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg hR.le
    intro r hr
    exact mul_nonneg (pow_nonneg hr.1 k) (sq_nonneg _)
  have hEn : 0 ≤ E := add_nonneg (hnon 11 (deriv F)) (hnon 11 (deriv G))
  have hineq : -(∫ r in (0 : ℝ)..R, r ^ 11 * (star (F r) * H r).re) -
      (∫ r in (0 : ℝ)..R, r ^ 11 * (star (G r) * J r).re) ≤ C * I + E / 2 := by
    have hc1 : Continuous (fun r => r ^ 11 * (star (F r) * H r).re) := by fun_prop
    have hc2 : Continuous (fun r => r ^ 11 * (star (G r) * J r).re) := by fun_prop
    have hcf : Continuous (fun r => r ^ 11 * ‖F r‖ ^ 2) := by fun_prop
    have hcg : Continuous (fun r => r ^ 11 * ‖G r‖ ^ 2) := by fun_prop
    have hcdf : Continuous (fun r => r ^ 11 * ‖deriv F r‖ ^ 2) := by
      exact (continuous_id.pow 11).mul ((hF.continuous_deriv (by norm_num)).norm.pow 2)
    have hcdg : Continuous (fun r => r ^ 11 * ‖deriv G r‖ ^ 2) := by
      exact (continuous_id.pow 11).mul ((hG.continuous_deriv (by norm_num)).norm.pow 2)
    have hi := intervalIntegral.integral_mono_on hR.le
      ((hc1.add hc2).neg.intervalIntegrable (μ := volume) 0 R)
      ((((hcf.add hcg).const_mul C).add ((hcdf.add hcdg).div_const 2)).intervalIntegrable (μ := volume) 0 R)
      (fun r hr => by
        dsimp only [Pi.add_apply, Pi.neg_apply]
        have hh := mul_le_mul_of_nonneg_left (hbound r hr) (pow_nonneg hr.1 11)
        convert hh using 1 <;> ring)
    change (∫ r in (0 : ℝ)..R, -(r ^ 11 * (star (F r) * H r).re +
      r ^ 11 * (star (G r) * J r).re)) ≤
      (∫ r in (0 : ℝ)..R, C * (r ^ 11 * ‖F r‖ ^ 2 + r ^ 11 * ‖G r‖ ^ 2) +
        (r ^ 11 * ‖deriv F r‖ ^ 2 + r ^ 11 * ‖deriv G r‖ ^ 2) / 2) at hi
    have hci : IntervalIntegrable (fun r => C * (r ^ 11 * ‖F r‖ ^ 2 +
        r ^ 11 * ‖G r‖ ^ 2)) volume 0 R := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hdi : IntervalIntegrable (fun r => (r ^ 11 * ‖deriv F r‖ ^ 2 +
        r ^ 11 * ‖deriv G r‖ ^ 2) / 2) volume 0 R := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_add (hc1.intervalIntegrable (μ := volume) 0 R)
        (hc2.intervalIntegrable (μ := volume) 0 R),
      intervalIntegral.integral_add hci hdi,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_add (hcf.intervalIntegrable (μ := volume) 0 R)
        (hcg.intervalIntegrable (μ := volume) 0 R),
      intervalIntegral.integral_add (hcdf.intervalIntegrable (μ := volume) 0 R)
        (hcdg.intervalIntegrable (μ := volume) 0 R)] at hi
    dsimp only [I, E]
    linarith
  have hE : E ≤ C * I + E / 2 := by
    have hpF := mul_nonneg heta (hnon 9 F)
    have hpG := mul_nonneg heta (hnon 9 G)
    dsimp only [E]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hPN hC
  have heq : E = 0 := by nlinarith
  have hzeroF : (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv F r‖ ^ 2) = 0 := by
    dsimp only [E] at heq
    linarith [hnon 11 (deriv F), hnon 11 (deriv G)]
  have hzeroG : (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv G r‖ ^ 2) = 0 := by
    dsimp only [E] at heq
    linarith [hnon 11 (deriv F), hnon 11 (deriv G)]
  exact fun r hr => ⟨homogeneousRegular_gradient_zero R hR F (hF.of_le (by norm_num)) hFR hzeroF r hr,
    homogeneousRegular_gradient_zero R hR G (hG.of_le (by norm_num)) hGR hzeroG r hr⟩

end DefocusingNLS

end OAI
