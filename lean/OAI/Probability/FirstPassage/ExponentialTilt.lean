import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFPP
open Real Set MeasureTheory

noncomputable def exponentialLikelihood (ρ x : ℝ) : ℝ :=
  ρ * exp (-(ρ - 1) * x)

theorem likelihood_second_moment_integral (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    (∫ x : ℝ in Ioi 0, (exponentialLikelihood ρ x) ^ 2 * exp (-x)) =
      ρ ^ 2 / (2 * ρ - 1) := by
  have hfun : (fun x : ℝ => (exponentialLikelihood ρ x) ^ 2 * exp (-x)) =
      (fun x : ℝ => ρ ^ 2 * exp ((-(2 * ρ - 1)) * x)) := by
    funext x
    unfold exponentialLikelihood
    rw [mul_pow, ← exp_nat_mul, mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, exp_zero, neg_div_neg_eq]
  ring

theorem tilted_rate_second_moment (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    (∫ x : ℝ in Ioi 0, (exponentialLikelihood (1 / (1 - δ)) x) ^ 2 * exp (-x)) =
      1 / (1 - δ ^ 2) := by
  have hden : 0 < 1 - δ := by linarith
  have hrate : 1 / 2 < 1 / (1 - δ) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  rw [likelihood_second_moment_integral _ hrate]
  have hden' : 0 < 1 - δ ^ 2 := by nlinarith
  field_simp [ne_of_gt hden, ne_of_gt hden']
  ring_nf
  field_simp [show 1 + δ ≠ 0 by linarith]
  ring

theorem likelihood_power_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) (M : ℕ) :
    (1 / (1 - δ ^ 2)) ^ M ≤ exp (2 * M * δ ^ 2) := by
  have hden : 0 < 1 - δ ^ 2 := by nlinarith
  have hsmall : 0 ≤ 1 - 2 * δ ^ 2 := by nlinarith
  have hrat : 1 / (1 - δ ^ 2) ≤ 2 * δ ^ 2 + 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg δ) hsmall]
  have he : 1 / (1 - δ ^ 2) ≤ exp (2 * δ ^ 2) :=
    hrat.trans (add_one_le_exp _)
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 / (1 - δ ^ 2) by positivity) he M
  calc
    (1 / (1 - δ ^ 2)) ^ M ≤ exp (2 * δ ^ 2) ^ M := hp
    _ = exp (2 * M * δ ^ 2) := by rw [← exp_nat_mul]; congr 1; ring

end PlanarFPP

end OAI
