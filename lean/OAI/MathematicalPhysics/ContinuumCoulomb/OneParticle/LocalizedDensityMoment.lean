import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombTranslation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarExponentialEnvelope

namespace OAI

/-! A fixed finite second moment of the actual localized probability density.
It supplies a polynomial finite-box truncation radius, uniformly in the
relative displacement appearing in a direct Coulomb coefficient. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem quadratic_exponential_bound {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-(1 / 2 : ℝ) * t) ≤ 343 := by
  have h := exponential_inverse_cubic_bound (by norm_num : (0 : ℝ) < 1 / 2) ht
  norm_num at h
  have hp : 0 < (1 + t) ^ 3 := by positivity
  have hm := (le_div_iff₀ hp).mp h
  have hpoly : t ^ 2 ≤ (1 + t) ^ 3 := by
    nlinarith [mul_nonneg ht (sq_nonneg t), sq_nonneg t]
  calc
    _ = Real.exp (-(1 / 2 : ℝ) * t) * t ^ 2 := mul_comm _ _
    _ ≤ Real.exp (-(1 / 2 : ℝ) * t) * (1 + t) ^ 3 :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ ≤ 343 := by simpa only [neg_mul] using hm

theorem planarResolventMode_second_moment_integrable :
    Integrable (fun r : PlanarPosition => ‖r‖ ^ 2 * planarResolventMode r ^ 2) := by
  let C := planarExponentialConstant (1 / 2) ^ 2 * 343
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ((planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C).mono'
    ((continuous_norm.pow 2).mul (planarResolventMode_C7.continuous.pow 2)).aestronglyMeasurable
  filter_upwards [] with r
  change ‖‖r‖ ^ 2 * planarResolventMode r ^ 2‖ ≤ C * Real.exp (-(1 / 2 : ℝ) * ‖r‖)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hmode := pow_le_pow_left₀ (planarResolventMode_positive r).le
    (planarResolventMode_exponential_envelope (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) r) 2
  have hsq : Real.exp (-(1 / 2 : ℝ) * ‖r‖) ^ 2 =
      Real.exp (-(1 / 2 : ℝ) * ‖r‖) * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by ring
  rw [mul_pow, hsq] at hmode
  calc
    _ ≤ ‖r‖ ^ 2 * (planarExponentialConstant (1 / 2) ^ 2 *
        (Real.exp (-(1 / 2 : ℝ) * ‖r‖) * Real.exp (-(1 / 2 : ℝ) * ‖r‖))) :=
      mul_le_mul_of_nonneg_left hmode (sq_nonneg _)
    _ = (planarExponentialConstant (1 / 2) ^ 2 *
        (‖r‖ ^ 2 * Real.exp (-(1 / 2 : ℝ) * ‖r‖))) *
          Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by ring
    _ ≤ C * Real.exp (-(1 / 2 : ℝ) * ‖r‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (quadratic_exponential_bound (norm_nonneg r))
          (sq_nonneg _)) (Real.exp_pos _).le

theorem normalizedPlanarMode_second_moment_integrable :
    Integrable (fun r : PlanarPosition => ‖r‖ ^ 2 * normalizedPlanarMode r ^ 2) := by
  simp_rw [normalizedPlanarMode, div_pow, ← mul_div_assoc]
  exact planarResolventMode_second_moment_integrable.div_const _

theorem localizedDensity_second_moment_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun x : Position => ‖x‖ ^ 2 * localizedDensity freq 0 x) := by
  have hsplit : Integrable (fun p : SplitPosition =>
      (‖p.1‖ ^ 2 + p.2 ^ 2) * localizedMode freq 0 p ^ 2) := by
    have hp := normalizedPlanarMode_second_moment_integrable.mul_prod
      (verticalMode_square_integrable hfreq)
    have hz := normalizedPlanarMode_square_integrable.mul_prod
      (verticalMode_moment_integrable hfreq 2)
    convert hp.add hz using 1
    funext p
    simp only [localizedMode, sub_zero, mul_pow, Pi.add_apply]
    ring
  have hc := positionSplitCoordinates_measurePreserving.integrable_comp_of_integrable hsplit
  convert hc using 1
  funext x
  simp only [Function.comp_apply, localizedDensity, continuumLocalizedMode,
    positionSplitCoordinates_norm_sq]

def localizedDensitySecondMoment (freq : ℝ) : ℝ :=
  ∫ x : Position, ‖x‖ ^ 2 * localizedDensity freq 0 x

theorem localizedDensitySecondMoment_nonnegative (freq : ℝ) :
    0 ≤ localizedDensitySecondMoment freq :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (localizedDensity_nonnegative _ _ _))

theorem localizedDensity_tail_of_norm {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq 0 x) ≤ localizedDensitySecondMoment freq / R ^ 2 := by
  have hw := localizedDensity_second_moment_integrable hfreq
  have hd := (localizedDensity_integrable hfreq 0).const_mul (R ^ 2)
  have hle := setIntegral_mono_on hd.integrableOn hw.integrableOn hS.compl
    (fun x hx => mul_le_mul_of_nonneg_right
      (sq_le_sq₀ hR.le (norm_nonneg x) |>.mpr (hout x hx))
      (localizedDensity_nonnegative freq 0 x))
  have hfull := integral_mono_measure (μ := volume.restrict Sᶜ)
    Measure.restrict_le_self (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (sq_nonneg ‖x‖) (localizedDensity_nonnegative freq 0 x))) hw
  rw [integral_const_mul] at hle
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  simpa only [localizedDensitySecondMoment, mul_comm] using hle.trans hfull

end ContinuumCoulomb

end

end OAI
