import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarLowerTail
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeDerivatives
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

private theorem forcing_lipschitz_exists : ∃ C : ℝ≥0, LipschitzWith C planarForcing :=
  ContDiff.lipschitzWith_of_hasCompactSupport planarForcing_hasCompactSupport
    planarForcing_C7 (by norm_num)

def planarForcingLipschitzConstant : ℝ≥0 := Classical.choose forcing_lipschitz_exists

theorem planarForcing_lipschitz : LipschitzWith planarForcingLipschitzConstant planarForcing :=
  Classical.choose_spec forcing_lipschitz_exists

theorem planarResolventMode_integrand_integrable (r : PlanarPosition) :
    Integrable (fun b => planarResolventKernel b * planarForcing (r - b)) := by
  apply planarResolventKernel_integrable.mul_bdd (c := 1)
    (planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun b => by
    change ‖planarForcing (r - b)‖ ≤ (1 : ℝ)
    rw [Real.norm_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

theorem planarResolventMode_norm_sub (x y : PlanarPosition) :
    ‖planarResolventMode x - planarResolventMode y‖ ≤
      planarForcingLipschitzConstant * ‖x - y‖ := by
  unfold planarResolventMode
  rw [← integral_sub (planarResolventMode_integrand_integrable x)
    (planarResolventMode_integrand_integrable y)]
  have h := norm_integral_le_of_norm_le
    (f := fun b => planarResolventKernel b * planarForcing (x - b) -
      planarResolventKernel b * planarForcing (y - b))
    (planarResolventKernel_integrable.mul_const
      ((planarForcingLipschitzConstant : ℝ) * ‖x - y‖))
    (Filter.Eventually.of_forall (fun b => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (planarResolventKernel_nonnegative b)]
      apply mul_le_mul_of_nonneg_left _ (planarResolventKernel_nonnegative b)
      have h := planarForcing_lipschitz.norm_sub_le (x - b) (y - b)
      simpa only [show x - b - (y - b) = x - y by abel] using h))
  simpa only [integral_mul_const, planarResolventKernel_integral, one_mul] using h

theorem planarResolventMode_lipschitz :
    LipschitzWith planarForcingLipschitzConstant planarResolventMode :=
  LipschitzWith.of_dist_le_mul (by simpa only [dist_eq_norm] using planarResolventMode_norm_sub)

def planarHoppingIntegrand (d : ℝ) (r : PlanarPosition) : ℝ :=
  planarForcing r * planarResolventMode (r - d • planarAxis 0)

theorem planarHoppingIntegrand_continuous (d : ℝ) : Continuous (planarHoppingIntegrand d) :=
  planarForcing_C7.continuous.mul
    (planarResolventMode_C7.continuous.comp (continuous_id.sub continuous_const))

theorem planarHoppingIntegrand_integrable (d : ℝ) : Integrable (planarHoppingIntegrand d) :=
  (planarHoppingIntegrand_continuous d).integrable_of_hasCompactSupport
    planarForcing_hasCompactSupport.mul_right

theorem planarHoppingIntegrand_nonnegative (d : ℝ) (r : PlanarPosition) :
    0 ≤ planarHoppingIntegrand d r :=
  mul_nonneg (planarForcing_nonnegative r) (planarResolventMode_positive _).le

def planarHopping (d : ℝ) : ℝ :=
  (∫ r, planarHoppingIntegrand d r) / (2 * ∫ r, planarResolventMode r ^ 2)

theorem planarHopping_positive (d : ℝ) : 0 < planarHopping d := by
  apply div_pos _ (mul_pos (by norm_num) planarResolventMode_square_integral_positive)
  apply integral_pos_of_integrable_nonneg_nonzero
    (planarHoppingIntegrand_continuous d) (planarHoppingIntegrand_integrable d)
    (planarHoppingIntegrand_nonnegative d)
  change planarForcing 0 * planarResolventMode (0 - d • planarAxis 0) ≠ 0
  rw [planarForcing_zero, one_mul]
  exact (planarResolventMode_positive _).ne'

theorem planarAxis_zero_norm : ‖planarAxis 0‖ = 1 := by
  simp [planarAxis]

def planarHoppingLipschitzConstant : ℝ≥0 :=
  ⟨planarForcingLipschitzConstant * (∫ r, planarForcing r) /
      (2 * ∫ r, planarResolventMode r ^ 2), by
    exact div_nonneg (mul_nonneg (NNReal.coe_nonneg _) planarForcing_integral_positive.le)
      (mul_nonneg (by norm_num) planarResolventMode_square_integral_positive.le)⟩

theorem planarHopping_norm_sub (d e : ℝ) :
    ‖planarHopping d - planarHopping e‖ ≤ planarHoppingLipschitzConstant * ‖d - e‖ := by
  have hden : 0 < 2 * ∫ r, planarResolventMode r ^ 2 :=
    mul_pos (by norm_num) planarResolventMode_square_integral_positive
  have hb (r : PlanarPosition) :
      ‖planarHoppingIntegrand d r - planarHoppingIntegrand e r‖ ≤
        planarForcing r * (planarForcingLipschitzConstant * ‖d - e‖) := by
    unfold planarHoppingIntegrand
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (planarForcing_nonnegative r)]
    apply mul_le_mul_of_nonneg_left _ (planarForcing_nonnegative r)
    have h := planarResolventMode_norm_sub (r - d • planarAxis 0) (r - e • planarAxis 0)
    have heq : ‖r - d • planarAxis 0 - (r - e • planarAxis 0)‖ = ‖d - e‖ := by
      rw [show r - d • planarAxis 0 - (r - e • planarAxis 0) =
        (e - d) • planarAxis 0 by rw [sub_smul]; abel,
        norm_smul, planarAxis_zero_norm, mul_one, Real.norm_eq_abs, abs_sub_comm]
      rfl
    simpa only [heq] using h
  have hi := norm_integral_le_of_norm_le
    (planarForcing_integrable.mul_const ((planarForcingLipschitzConstant : ℝ) * ‖d - e‖))
    (Filter.Eventually.of_forall hb)
  rw [integral_sub (planarHoppingIntegrand_integrable d) (planarHoppingIntegrand_integrable e),
    integral_mul_const] at hi
  unfold planarHopping
  rw [← sub_div, norm_div, Real.norm_of_nonneg hden.le]
  change _ ≤ (planarForcingLipschitzConstant * (∫ r, planarForcing r) /
    (2 * ∫ r, planarResolventMode r ^ 2)) * ‖d - e‖
  calc
    _ ≤ ((∫ r, planarForcing r) * (planarForcingLipschitzConstant * ‖d - e‖)) /
        (2 * ∫ r, planarResolventMode r ^ 2) := div_le_div_of_nonneg_right hi hden.le
    _ = _ := by ring

theorem planarHopping_lipschitz : LipschitzWith planarHoppingLipschitzConstant planarHopping :=
  LipschitzWith.of_dist_le_mul (by simpa only [dist_eq_norm] using planarHopping_norm_sub)

end ContinuumCoulomb

end

end OAI
