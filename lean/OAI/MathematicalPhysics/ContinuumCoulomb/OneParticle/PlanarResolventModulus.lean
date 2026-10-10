import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarForcingModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHopping

namespace OAI

/-! Explicit moduli for numerical normalization and contact integrals.
The constants come from the actual compact forcing and mass-one kernel. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventMode_norm_sub_explicit (x y : PlanarPosition) :
    |planarResolventMode x - planarResolventMode y| ≤ 32 * ‖x - y‖ := by
  unfold planarResolventMode
  rw [← integral_sub (planarResolventMode_integrand_integrable x)
    (planarResolventMode_integrand_integrable y)]
  have h := norm_integral_le_of_norm_le
    (f := fun b => planarResolventKernel b * planarForcing (x - b) -
      planarResolventKernel b * planarForcing (y - b))
    (planarResolventKernel_integrable.mul_const (32 * ‖x - y‖))
    (Filter.Eventually.of_forall (fun b => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (planarResolventKernel_nonnegative b),
        Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (planarResolventKernel_nonnegative b)
      simpa only [show x - b - (y - b) = x - y by abel] using
        planarForcing_norm_sub_explicit (x - b) (y - b)))
  simpa only [integral_mul_const, planarResolventKernel_integral, one_mul,
    Real.norm_eq_abs] using h

theorem planarResolventMode_square_norm_sub (x y : PlanarPosition) :
    |planarResolventMode x ^ 2 - planarResolventMode y ^ 2| ≤ 64 * ‖x - y‖ := by
  have hx := (planarResolventMode_positive x).le
  have hy := (planarResolventMode_positive y).le
  have hsum : 0 ≤ planarResolventMode x + planarResolventMode y := add_nonneg hx hy
  have hsum' : planarResolventMode x + planarResolventMode y ≤ 2 :=
    by linarith [planarResolventMode_le_one x, planarResolventMode_le_one y]
  rw [show planarResolventMode x ^ 2 - planarResolventMode y ^ 2 =
    (planarResolventMode x - planarResolventMode y) *
      (planarResolventMode x + planarResolventMode y) by ring,
    abs_mul, abs_of_nonneg hsum]
  calc
    _ ≤ (32 * ‖x - y‖) * 2 :=
      mul_le_mul (planarResolventMode_norm_sub_explicit x y) hsum'
        hsum (by positivity)
    _ = _ := by ring

theorem planarHoppingIntegrand_norm_sub_explicit (d : ℝ) (x y : PlanarPosition) :
    |planarHoppingIntegrand d x - planarHoppingIntegrand d y| ≤ 64 * ‖x - y‖ := by
  have hx := planarForcing_nonnegative x
  have hy := planarForcing_nonnegative y
  have hz := (planarResolventMode_positive (y - d • planarAxis 0)).le
  have ha := planarResolventMode_le_one (y - d • planarAxis 0)
  have hb := planarForcing_le_one x
  have heq : planarHoppingIntegrand d x - planarHoppingIntegrand d y =
      planarForcing x * (planarResolventMode (x - d • planarAxis 0) -
        planarResolventMode (y - d • planarAxis 0)) +
      (planarForcing x - planarForcing y) * planarResolventMode (y - d • planarAxis 0) := by
    unfold planarHoppingIntegrand
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hz]
  have hr : |planarResolventMode (x - d • planarAxis 0) -
      planarResolventMode (y - d • planarAxis 0)| ≤ 32 * ‖x - y‖ := by
    simpa only [show x - d • planarAxis 0 - (y - d • planarAxis 0) = x - y by abel] using
      planarResolventMode_norm_sub_explicit (x - d • planarAxis 0) (y - d • planarAxis 0)
  have h₁ := mul_le_mul hb hr (abs_nonneg _) zero_le_one
  have h₂ := mul_le_mul (planarForcing_norm_sub_explicit x y) ha hz (by positivity)
  linarith

end ContinuumCoulomb

end

end OAI
