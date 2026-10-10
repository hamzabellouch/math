import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarExponentialEnvelope
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarNormalized

namespace OAI

/-! Actual normalized planar orbitals have overlap bounded at rate 0.9,
uniformly over every pair of centers. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def normalizedPlanarExponentialConstant (a : ℝ) : ℝ :=
  planarExponentialConstant a / Real.sqrt (∫ r, planarResolventMode r ^ 2)

theorem normalizedPlanarExponentialConstant_positive {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) :
    0 < normalizedPlanarExponentialConstant a :=
  div_pos (planarExponentialConstant_positive ha ha₁)
    (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive)

theorem normalizedPlanarMode_exponential_envelope {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1)
    (r : PlanarPosition) :
    normalizedPlanarMode r ≤ normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r‖) := by
  have h := div_le_div_of_nonneg_right (planarResolventMode_exponential_envelope ha ha₁ r)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  convert h using 1
  · rfl
  · unfold normalizedPlanarExponentialConstant
    ring

def planarModeOverlap (u v : PlanarPosition) : ℝ :=
  ∫ r, normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v)

theorem planarModeOverlap_integrable (u v : PlanarPosition) :
    Integrable (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v)) :=
  (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)).integrable_mul
    (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume v))

theorem planarModeOverlap_nonnegative (u v : PlanarPosition) : 0 ≤ planarModeOverlap u v :=
  integral_nonneg (fun _ => mul_nonneg (normalizedPlanarMode_positive _).le (normalizedPlanarMode_positive _).le)

theorem planarModeOverlap_diagonal (u : PlanarPosition) : planarModeOverlap u u = 1 := by
  unfold planarModeOverlap
  simp_rw [← pow_two]
  rw [integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized]

theorem planarModeOverlap_envelope {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha₁ : a < 1)
    (u v : PlanarPosition) :
    planarModeOverlap u v ≤
      (normalizedPlanarExponentialConstant a ^ 2 *
        (∫ r : PlanarPosition, Real.exp (-(a - b) * ‖r‖))) * Real.exp (-b * ‖u - v‖) := by
  have ha : 0 ≤ a := le_trans hb hba.le
  have hC := (normalizedPlanarExponentialConstant_positive ha ha₁).le
  have hpt (r : PlanarPosition) :
      normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v) ≤
        (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖)) *
          Real.exp (-(a - b) * ‖r - u‖) := by
    have ht : ‖u - v‖ ≤ ‖r - u‖ + ‖r - v‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u r] using dist_triangle u r v
    have hs := mul_le_mul_of_nonneg_left ht hb
    have he : -a * (‖r - u‖ + ‖r - v‖) ≤ -b * ‖u - v‖ + -(a - b) * ‖r - u‖ := by
      nlinarith [mul_nonneg (sub_pos.mpr hba).le (norm_nonneg (r - v))]
    calc
      _ ≤ (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - u‖)) *
          (normalizedPlanarExponentialConstant a * Real.exp (-a * ‖r - v‖)) :=
        mul_le_mul (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_exponential_envelope ha ha₁ _)
          (normalizedPlanarMode_positive _).le (mul_nonneg hC (Real.exp_pos _).le)
      _ = normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-a * (‖r - u‖ + ‖r - v‖)) := by
        rw [show -a * (‖r - u‖ + ‖r - v‖) = -a * ‖r - u‖ + -a * ‖r - v‖ by ring,
          Real.exp_add]
        ring
      _ ≤ normalizedPlanarExponentialConstant a ^ 2 *
          Real.exp (-b * ‖u - v‖ + -(a - b) * ‖r - u‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
      _ = _ := by rw [Real.exp_add]; ring
  have hi := ((planar_exp_norm_integrable (sub_pos.mpr hba)).comp_sub_right u).const_mul
    (normalizedPlanarExponentialConstant a ^ 2 * Real.exp (-b * ‖u - v‖))
  have h := integral_mono (planarModeOverlap_integrable u v) hi hpt
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun r : PlanarPosition => Real.exp (-(a - b) * ‖r‖)) u] at h
  exact h.trans_eq (by ring)

def planarOverlapConstant : ℝ := normalizedPlanarExponentialConstant (19 / 20) ^ 2 *
  (∫ r : PlanarPosition, Real.exp (-(1 / 20 : ℝ) * ‖r‖))

theorem planarOverlapConstant_nonnegative : 0 ≤ planarOverlapConstant :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem planarModeOverlap_decay (u v : PlanarPosition) :
    planarModeOverlap u v ≤ planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  have h := planarModeOverlap_envelope (a := 19 / 20) (b := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) u v
  norm_num only [show (19 / 20 : ℝ) - 9 / 10 = 1 / 20 by norm_num] at h
  exact h

end ContinuumCoulomb

end

end OAI
