import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGroundTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-! The manuscript's explicit planar forcing `(1-|r|²)₊¹⁶`, including finite
smoothness at its support boundary. The positive-part power is represented
by a polynomial plus a fractional power of a square, avoiding a nonsmooth
positive-part differentiation rule. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def positivePartSixteen (x : ℝ) : ℝ := max x 0 ^ 16

theorem positivePartSixteen_formula (x : ℝ) :
    positivePartSixteen x = (x ^ 16 + x * (x ^ 2 : ℝ) ^ (15 / 2 : ℝ)) / 2 := by
  have hp : (x ^ 2 : ℝ) ^ (15 / 2 : ℝ) = |x| ^ 15 := by
    rw [Real.rpow_div_two_eq_sqrt (15 : ℝ) (sq_nonneg x), Real.sqrt_sq_eq_abs]
    norm_cast
  rw [hp]
  rcases le_total 0 x with hx | hx
  · rw [positivePartSixteen, max_eq_left hx, abs_of_nonneg hx]
    ring
  · rw [positivePartSixteen, max_eq_right hx, abs_of_nonpos hx]
    norm_num
    ring

theorem positivePartSixteen_C7 : ContDiff ℝ 7 positivePartSixteen := by
  have hs : ContDiff ℝ 7 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  have hp : ContDiff ℝ 7 (fun x : ℝ => (x ^ 2 : ℝ) ^ (15 / 2 : ℝ)) :=
    hs.rpow_const_of_le (by norm_num : (7 : ℝ) ≤ 15 / 2)
  have heq : positivePartSixteen =
      fun x : ℝ => (x ^ 16 + x * (x ^ 2 : ℝ) ^ (15 / 2 : ℝ)) / 2 :=
    funext positivePartSixteen_formula
  rw [heq]
  exact ((contDiff_id.pow 16).add (contDiff_id.mul hp)).div_const 2

def planarForcing (r : PlanarPosition) : ℝ := positivePartSixteen (1 - ‖r‖ ^ 2)

theorem planarForcing_C7 : ContDiff ℝ 7 planarForcing :=
  positivePartSixteen_C7.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem planarForcing_nonnegative (r : PlanarPosition) : 0 ≤ planarForcing r :=
  pow_nonneg (le_max_right _ _) _

theorem planarForcing_le_one (r : PlanarPosition) : planarForcing r ≤ 1 := by
  have hm : max (1 - ‖r‖ ^ 2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg ‖r‖]) zero_le_one
  change max (1 - ‖r‖ ^ 2) 0 ^ 16 ≤ 1
  simpa only [one_pow] using pow_le_pow_left₀ (le_max_right _ _) hm 16

theorem planarForcing_zero_of_norm_ge_one {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarForcing r = 0 := by
  have hsq : 1 ≤ ‖r‖ ^ 2 := by nlinarith
  rw [planarForcing, positivePartSixteen, max_eq_right (by linarith)]
  norm_num

theorem planarForcing_support : tsupport planarForcing ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro r hr
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hr (planarForcing_zero_of_norm_ge_one (by linarith))

theorem planarForcing_hasCompactSupport : HasCompactSupport planarForcing :=
  (isCompact_closedBall (0 : PlanarPosition) 1).of_isClosed_subset
    (isClosed_tsupport _) planarForcing_support

theorem planarForcing_zero : planarForcing 0 = 1 := by
  norm_num [planarForcing, positivePartSixteen]

theorem planarForcing_integrable : Integrable planarForcing :=
  planarForcing_C7.continuous.integrable_of_hasCompactSupport planarForcing_hasCompactSupport

theorem planarForcing_integral_positive : 0 < ∫ r, planarForcing r :=
  integral_pos_of_integrable_nonneg_nonzero planarForcing_C7.continuous
    planarForcing_integrable planarForcing_nonnegative (by rw [planarForcing_zero]; norm_num)

end ContinuumCoulomb

end

end OAI
