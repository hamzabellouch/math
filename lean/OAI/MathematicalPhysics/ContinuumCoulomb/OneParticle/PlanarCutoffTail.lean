import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSiteCutoffs
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarOverlap

namespace OAI

/-! The actual site cutoff changes its normalized ground mode by an
exponentially small L2 vector. This controls the rank-one terms in IMS. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planar_l2_pair_sq_le (f g : PlanarPosition → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    (∫ x, f x * g x)^2 ≤ (∫ x, f x^2) * (∫ x, g x^2) := by
  have hpair (a b : PlanarPosition → ℝ) (ha : MemLp a 2) (hb : MemLp b 2) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply, conj_trivial]
    ring
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hpair f g hf hg, hpair f f hf hf, hpair g g hg hg] at h
  simpa only [pow_two] using h

def planarSiteCutoffError (D : ℝ) (u x : PlanarPosition) : ℝ :=
  (Real.sin (planarSiteAngle D u x) - 1) * normalizedPlanarMode (x-u)

theorem planarSiteCutoff_deviation_bound (D : ℝ) (u x : PlanarPosition) :
    |Real.sin (planarSiteAngle D u x) - 1| ≤ 2 := by
  have h := abs_sub (Real.sin (planarSiteAngle D u x)) (1 : ℝ)
  have hs := Real.abs_sin_le_one (planarSiteAngle D u x)
  norm_num only [abs_one] at h
  linarith

theorem planarSiteCutoffError_memLp (D : ℝ) (u : PlanarPosition) :
    MemLp (planarSiteCutoffError D u) 2 := by
  have hm := normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  apply hm.of_le_mul (c := 2)
    ((((planarSiteAngle_C1 D u).sin.continuous.sub continuous_const).mul
      (normalizedPlanarMode_C7.continuous.comp (continuous_id.sub continuous_const))).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(Real.sin (planarSiteAngle D u x) - 1) * normalizedPlanarMode (x-u)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (planarSiteCutoff_deviation_bound D u x) (norm_nonneg _)

def planarSiteTailConstant : ℝ :=
  4 * normalizedPlanarExponentialConstant (19/20) ^ 2 *
    ∫ r : PlanarPosition, Real.exp (-(19/20 : ℝ) * ‖r‖)

theorem planarSiteTailConstant_nonnegative : 0 ≤ planarSiteTailConstant := by
  unfold planarSiteTailConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem planarSiteCutoffError_square_bound {D : ℝ} (hD : 0 < D) (u x : PlanarPosition) :
    planarSiteCutoffError D u x ^ 2 ≤
      (4 * normalizedPlanarExponentialConstant (19/20)^2 * Real.exp (-(19/20 : ℝ) * (D/8))) *
        Real.exp (-(19/20 : ℝ) * ‖x-u‖) := by
  by_cases hx : ‖x-u‖ ≤ D/8
  · rw [planarSiteCutoffError, planarSiteAngle_inner hD u x hx, Real.sin_pi_div_two,
      sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hr : D/8 ≤ ‖x-u‖ := (le_of_not_ge hx)
    have hdev : (Real.sin (planarSiteAngle D u x) - 1)^2 ≤ (4 : ℝ) := by
      have h := planarSiteCutoff_deviation_bound D u x
      have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
      simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using hs
    have hmode := pow_le_pow_left₀ (normalizedPlanarMode_positive (x-u)).le
      (normalizedPlanarMode_exponential_envelope (by norm_num : (0 : ℝ) ≤ 19/20)
        (by norm_num : (19/20 : ℝ) < 1) (x-u)) 2
    have he : Real.exp (-(19/20 : ℝ) * ‖x-u‖)^2 ≤
        Real.exp (-(19/20 : ℝ) * (D/8)) * Real.exp (-(19/20 : ℝ) * ‖x-u‖) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      norm_num only [Nat.cast_ofNat]
      linarith
    rw [mul_pow] at hmode
    have hmode' := hmode.trans (mul_le_mul_of_nonneg_left he
      (sq_nonneg (normalizedPlanarExponentialConstant (19/20))))
    unfold planarSiteCutoffError
    rw [mul_pow]
    calc
      _ ≤ 4 * (normalizedPlanarExponentialConstant (19/20)^2 *
          (Real.exp (-(19/20 : ℝ) * (D/8)) * Real.exp (-(19/20 : ℝ) * ‖x-u‖))) :=
        mul_le_mul hdev hmode' (sq_nonneg _) (by norm_num)
      _ = _ := by ring

theorem planarSiteCutoffError_integral_bound {D : ℝ} (hD : 0 < D) (u : PlanarPosition) :
    (∫ x, planarSiteCutoffError D u x ^ 2) ≤
      planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8)) := by
  have hi : Integrable (fun x => planarSiteCutoffError D u x ^ 2) :=
    (memLp_two_iff_integrable_sq (planarSiteCutoffError_memLp D u).aestronglyMeasurable).mp
      (planarSiteCutoffError_memLp D u)
  have he := ((planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 19/20)).comp_sub_right u).const_mul
    (4 * normalizedPlanarExponentialConstant (19/20)^2 * Real.exp (-(19/20 : ℝ) * (D/8)))
  have h := integral_mono hi he (planarSiteCutoffError_square_bound hD u)
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun r : PlanarPosition => Real.exp (-(19/20 : ℝ) * ‖r‖)) u] at h
  convert h using 1
  unfold planarSiteTailConstant
  ring

end ContinuumCoulomb

end

end OAI
