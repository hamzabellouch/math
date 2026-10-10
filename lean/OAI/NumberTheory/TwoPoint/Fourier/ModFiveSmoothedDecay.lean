import OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronParameters
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! Exponential decay for the actual triangularly smoothed nonprincipal
Mangoldt sums, obtained by the explicit Perron height exp(sqrt(log x)). -/

namespace TwoPointCorrelations

open Filter

lemma modFive_contour_parameter_bound {a C D y : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hC : 0 < C) (hD : 0 < D) (hy : 2 ≤ y) :
    4 * Real.pi * C * Real.log (Real.exp y + 2) ^ 2 *
        (Real.exp (y ^ 2)) ^ (1 - a / Real.log (Real.exp y + 2)) +
      4 * C * Real.log (Real.exp y + 2) ^ 2 *
        (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 +
      2 * (1 / (1 / y ^ 2) + D) *
        (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
      (16 * Real.pi * C + 16 * C + 2 * (1 + D)) * y ^ 2 *
        Real.exp (y ^ 2 + 1 - a * y / 2) := by
  have hyp : 0 < y := by linarith
  obtain ⟨_, hHlo, hHhi⟩ := modFive_perron_height hy
  have hHpos : 0 < Real.log (Real.exp y + 2) := hyp.trans_le hHlo
  have hHsq : Real.log (Real.exp y + 2) ^ 2 ≤ 4 * y ^ 2 := by
    convert pow_le_pow_left₀ hHpos.le hHhi 2 using 1; ring
  have hleft := modFive_perron_left_power ha.le hyp hHpos hHhi
  have hright := modFive_perron_right_power hyp
  have hheight : (Real.exp y) ^ 2 = Real.exp (2 * y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let F := Real.exp (y ^ 2 + 1 - a * y / 2)
  have hF : 0 ≤ F := (Real.exp_pos _).le
  have h1 : 4 * Real.pi * C * Real.log (Real.exp y + 2) ^ 2 *
      (Real.exp (y ^ 2)) ^ (1 - a / Real.log (Real.exp y + 2)) ≤
        (16 * Real.pi * C * y ^ 2) * F := by
    have hp : (Real.exp (y ^ 2)) ^ (1 - a / Real.log (Real.exp y + 2)) ≤ F :=
      hleft.trans (Real.exp_le_exp.mpr (by linarith))
    have hc : 4 * Real.pi * C * Real.log (Real.exp y + 2) ^ 2 ≤
        16 * Real.pi * C * y ^ 2 := by
      convert mul_le_mul_of_nonneg_left hHsq
        (by positivity : 0 ≤ 4 * Real.pi * C) using 1; ring
    exact mul_le_mul hc hp (Real.rpow_nonneg (Real.exp_pos _).le _)
      (by positivity)
  have h2 : 4 * C * Real.log (Real.exp y + 2) ^ 2 *
      (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 ≤
        (16 * C * y ^ 2) * F := by
    have he : Real.exp (y ^ 2 + 1 - 2 * y) ≤ F := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [hright, hheight, mul_div_assoc, ← Real.exp_sub]
    have hc : 4 * C * Real.log (Real.exp y + 2) ^ 2 ≤ 16 * C * y ^ 2 := by
      convert mul_le_mul_of_nonneg_left hHsq (by positivity : 0 ≤ 4 * C)
        using 1; ring
    exact mul_le_mul hc
      he (Real.exp_pos _).le (by positivity)
  have h3 : 2 * (1 / (1 / y ^ 2) + D) *
      (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
        (2 * (1 + D) * y ^ 2) * F := by
    have he : Real.exp (y ^ 2 + 1 - y) ≤ F := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [one_div_one_div, hright, mul_div_assoc, ← Real.exp_sub]
    have hysq : 1 ≤ y ^ 2 := by nlinarith
    have hc : 2 * (y ^ 2 + D) ≤ 2 * (1 + D) * y ^ 2 := by
      nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hysq)]
    exact mul_le_mul hc
      he (Real.exp_pos _).le (by positivity)
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by dsimp [F]; ring)

/-- Uniform over the three nonprincipal characters. -/
theorem modFive_smoothed_decay_exp_square : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ y : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      (∀ n : ℕ, Real.exp (y ^ 2) ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ (Real.exp (y ^ 2))‖ ≤ Real.exp (y ^ 2 - c * y) := by
  obtain ⟨a, C, D, ha, ha4, hC, hD, hbound⟩ := modFive_smoothed_contour_bound
  let c := a / 4
  let K := 16 * Real.pi * C + 16 * C + 2 * (1 + D)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), modFive_perron_polynomial_absorption K c hc]
    with y hy hpoly χ hχ hxnat
  have hyp : 0 < y := by linarith
  have hδ : 0 < 1 / y ^ 2 := by positivity
  have hδ1 : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hx1 : 1 ≤ Real.exp (y ^ 2) := Real.one_le_exp (sq_nonneg y)
  have hmain := hbound χ hχ (Real.exp y) (Real.exp (y ^ 2)) (1 / y ^ 2)
    (modFive_perron_height hy).1 hx1 hδ hδ1 hxnat
  have hnum := modFive_contour_parameter_bound ha ha4 hC hD hy
  apply (hmain.trans hnum).trans
  have he : K * y ^ 2 * Real.exp (y ^ 2 + 1 - a * y / 2) =
      (K * y ^ 2 * Real.exp (1 - c * y)) * Real.exp (y ^ 2 - c * y) := by
    have hexp : y ^ 2 + 1 - a * y / 2 = (1 - c * y) + (y ^ 2 - c * y) := by
      dsimp [c]
      ring
    rw [hexp, Real.exp_add]
    ring
  change K * y ^ 2 * Real.exp (y ^ 2 + 1 - a * y / 2) ≤ _
  rw [he]
  exact (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le).trans_eq (one_mul _)

/-- The original real-cutoff form of the smoothed prime estimate. -/
theorem modFive_smoothed_decay : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ x‖ ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hbound⟩ := modFive_smoothed_decay_exp_square
  refine ⟨c, hc, ?_⟩
  have hcomp := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually hbound
  filter_upwards [hcomp, eventually_ge_atTop (1 : ℝ)] with x hmain hx χ hχ hxnat
  dsimp only [Function.comp_def] at hmain
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt (Real.log x) ^ 2 = Real.log x :=
    Real.sq_sqrt (Real.log_nonneg hx)
  have hb := hmain χ hχ (by simpa only [hs, Real.exp_log hxpos] using hxnat)
  simpa only [hs, Real.exp_log hxpos, sub_eq_add_neg, Real.exp_add,
    neg_mul] using hb

end TwoPointCorrelations

end OAI
