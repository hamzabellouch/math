import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarOverlap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarRadial

namespace OAI

/-! Actual well matrix elements. The well at the first orbital center gives
exactly the distance-dependent hopping; a well far from both centers gives
an error decaying at rate 1.9. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarWellMatrix (u v w : PlanarPosition) : ℝ :=
  ∫ r, normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v)

theorem planarWellMatrix_integrable (u v w : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) *
      normalizedPlanarMode (r - v)) := by
  apply (((normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const)).mul
    (manufacturedPlanarWell_C7.continuous.comp (continuous_id.sub continuous_const))).mul
    (normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
  exact (manufacturedPlanarWell_hasCompactSupport.comp_homeomorph (Homeomorph.subRight w)).mul_left.mul_right

theorem planarWellMatrix_hopping (u v : PlanarPosition) :
    planarWellMatrix u v u = -planarHopping ‖u - v‖ := by
  let S : ℝ := ∫ r, planarResolventMode r ^ 2
  have hS : 0 < S := planarResolventMode_square_integral_positive
  have hsqrt : Real.sqrt S ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hpt (r : PlanarPosition) :
      normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - u) * normalizedPlanarMode (r - v) =
        -(1 / (2 * S)) * (planarForcing (r - u) * planarResolventMode (r - v)) := by
    unfold normalizedPlanarMode manufacturedPlanarWell
    change (planarResolventMode (r - u) / Real.sqrt S) *
      (-planarForcing (r - u) / (2 * planarResolventMode (r - u))) *
      (planarResolventMode (r - v) / Real.sqrt S) = _
    field_simp [hsqrt, (planarResolventMode_positive (r - u)).ne', hS.ne']
    rw [Real.sq_sqrt hS.le]
    ring
  have hi : (∫ r, planarForcing (r - u) * planarResolventMode (r - v)) =
      ∫ r, planarForcing r * planarResolventMode (r - (v - u)) := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun r => planarForcing r * planarResolventMode (r - (v - u))) u
    convert h using 1
    congr 1
    funext r
    rw [show r - u - (v - u) = r - v by abel]
  unfold planarWellMatrix
  simp_rw [hpt]
  rw [integral_const_mul, hi, norm_sub_rev u v, ← planarHoppingAt_norm (v - u)]
  simp only [planarHoppingAt]
  change -(1 / (2 * S)) * _ = -(_ / (2 * S))
  ring

def planarWellMatrixConstant : ℝ :=
  normalizedPlanarExponentialConstant (19 / 20) ^ 2 * Real.exp (19 / 10) *
    (∫ r : PlanarPosition, |manufacturedPlanarWell r|)

theorem planarWellMatrixConstant_nonnegative : 0 ≤ planarWellMatrixConstant :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem planarWellMatrix_two_far {D : ℝ} (u v w : PlanarPosition)
    (hu : D ≤ ‖u - w‖) (hv : D ≤ ‖v - w‖) :
    |planarWellMatrix u v w| ≤ planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  let C := normalizedPlanarExponentialConstant (19 / 20)
  have hC : 0 ≤ C := (normalizedPlanarExponentialConstant_positive (by norm_num) (by norm_num)).le
  let B := C ^ 2 * Real.exp ((19 / 10 : ℝ) - (19 / 10 : ℝ) * D)
  have hpt (r : PlanarPosition) :
      ‖normalizedPlanarMode (r - u) * manufacturedPlanarWell (r - w) * normalizedPlanarMode (r - v)‖ ≤
        B * |manufacturedPlanarWell (r - w)| := by
    by_cases hw : manufacturedPlanarWell (r - w) = 0
    · simp only [hw, mul_zero, zero_mul, norm_zero, abs_zero, le_refl]
    have hs : ‖r - w‖ ≤ 1 := by
      have hm := (manufacturedPlanarWell_support.trans planarForcing_support)
        (subset_tsupport _ (show r - w ∈ Function.support manufacturedPlanarWell from hw))
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    have htu : ‖u - w‖ ≤ ‖r - u‖ + ‖r - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r w
    have htv : ‖v - w‖ ≤ ‖r - v‖ + ‖r - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev v r] using dist_triangle v r w
    have he : -(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖) ≤ 19 / 10 - (19 / 10 : ℝ) * D := by
      linarith
    have hp : normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤ B := by
      calc
        _ ≤ (C * Real.exp (-(19 / 20 : ℝ) * ‖r - u‖)) *
            (C * Real.exp (-(19 / 20 : ℝ) * ‖r - v‖)) :=
          mul_le_mul (normalizedPlanarMode_exponential_envelope (by norm_num) (by norm_num) _)
            (normalizedPlanarMode_exponential_envelope (by norm_num) (by norm_num) _)
            (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
        _ = C ^ 2 * Real.exp (-(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖)) := by
          rw [show -(19 / 20 : ℝ) * (‖r - u‖ + ‖r - v‖) =
            -(19 / 20 : ℝ) * ‖r - u‖ + -(19 / 20 : ℝ) * ‖r - v‖ by ring, Real.exp_add]
          ring
        _ ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg C)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (normalizedPlanarMode_positive _).le,
      Real.norm_of_nonneg (normalizedPlanarMode_positive _).le, Real.norm_eq_abs]
    convert mul_le_mul_of_nonneg_right hp (abs_nonneg (manufacturedPlanarWell (r - w))) using 1
    ring
  have hiW : Integrable manufacturedPlanarWell :=
    manufacturedPlanarWell_C7.continuous.integrable_of_hasCompactSupport manufacturedPlanarWell_hasCompactSupport
  have hi := (hiW.abs.comp_sub_right w).const_mul B
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_sub_right_eq_self (fun r : PlanarPosition => |manufacturedPlanarWell r|) w] at h
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  dsimp [B, C, planarWellMatrixConstant]
  rw [show (19 / 10 : ℝ) - (19 / 10 : ℝ) * D =
    (19 / 10 : ℝ) + -(19 / 10 : ℝ) * D by ring, Real.exp_add]
  ring

end ContinuumCoulomb

end

end OAI
