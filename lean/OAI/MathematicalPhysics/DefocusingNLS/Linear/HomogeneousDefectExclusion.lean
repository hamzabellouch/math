import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialPairL2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # The lower-order remainder cannot hide a transverse defect

This is the scalar final step after differentiating the original ODE:
the slowly varying value term is negligible compared with the forced
high-derivative power of a nonzero transverse component.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

theorem radial_pair_not_integrable_of_defect_remainder
    (f g : ℝ → ℂ) (E : ℝ → ℝ) (R beta d c C B : ℝ) (N : ℕ)
    (hc : 0 < c) (hC : 0 < C) (hb : -6 ≤ beta - d)
    (hgap : 0 < (N : ℝ) + beta - d)
    (hElower : ∀ᶠ r in atTop, c ≤ r ^ (2 * d) * E r)
    (hderiv : ∀ᶠ r in atTop, r ^ (2 * beta) * E r ≤
      C * homogeneousPairEnergy (f r, g r) + B * r ^ (-2 * (N : ℝ))) :
    ¬ (IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R) ∧
      IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) := by
  let delta := 2 * ((N : ℝ) + beta - d)
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hsmall : ∀ᶠ r : ℝ in atTop, B * r ^ (-delta) ≤ c / 2 := by
    have hh : Tendsto (fun r : ℝ => B * r ^ (-delta)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop (y := delta) hdelta).const_mul B
    have hh' := hh.eventually (gt_mem_nhds (half_pos hc))
    exact hh'.mono (fun _ h => h.le)
  apply radial_pair_not_integrable_of_energy_lower f g R (beta - d) (c / (2 * C))
    (by positivity) hb
  filter_upwards [hElower, hderiv, hsmall, eventually_gt_atTop (0 : ℝ)] with r hE hD hB hr
  have hp₁ : r ^ (2 * (beta - d)) * r ^ (2 * d) = r ^ (2 * beta) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hp₂ : r ^ (-delta) * r ^ (2 * (beta - d)) = r ^ (-2 * (N : ℝ)) := by
    rw [← Real.rpow_add hr]
    congr 1
    dsimp only [delta]
    ring
  have hE' := mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hr.le (2 * (beta - d)))
  rw [← mul_assoc, hp₁] at hE'
  have hB' := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hr.le (2 * (beta - d)))
  rw [mul_assoc B, hp₂] at hB'
  have hmain : c / 2 * r ^ (2 * (beta - d)) ≤ C * homogeneousPairEnergy (f r, g r) := by
    nlinarith [hE'.trans hD]
  apply (mul_le_mul_iff_right₀ hC).mp
  calc
    C * (c / (2 * C) * r ^ (2 * (beta - d))) = c / 2 * r ^ (2 * (beta - d)) := by
      field_simp
    _ ≤ C * homogeneousPairEnergy (f r, g r) := hmain

end DefocusingNLS

end OAI
