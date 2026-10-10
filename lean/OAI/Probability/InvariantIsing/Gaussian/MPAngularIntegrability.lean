import OAI.Probability.InvariantIsing.Gaussian.MPAngularMass

namespace OAI

/-! Integrability of the angular MP density, including the critical zero edge. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_critical_sine_integrable {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable (fun x => (sin x)^2/(b+b*cos x)) volume 0 Real.pi := by
  apply (((continuous_const.sub continuous_cos).div_const b).intervalIntegrable 0 Real.pi).congr_uIoo
  intro x hx
  rw [Set.uIoo_of_le pi_pos.le] at hx
  exact (mp_critical_sine_fraction hb hx).symm

lemma mp_angular_sine_integrable {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (fun x => (sin x)^2/(1+α+2*sqrt α*cos x)) volume 0 Real.pi := by
  by_cases he : α = 1
  · subst α
    simpa only [sqrt_one,mul_one,show (1 : ℝ)+1=2 by norm_num] using
      mp_critical_sine_integrable (b := 2) (by norm_num)
  · exact ((continuous_sin.pow 2).div
      (continuous_const.add (continuous_const.mul continuous_cos))
      (fun x => (mp_cos_denominator_pos (mp_centre_exceeds_radius hα.le he) x).ne')).intervalIntegrable 0 Real.pi

lemma mp_angular_denominator_nonneg {α : ℝ} (hα : 0 ≤ α) (x : ℝ) :
    0 ≤ 1+α+2*sqrt α*cos x := by
  have hs := sq_sqrt hα
  have hc := neg_one_le_cos x
  have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*sqrt α by positivity)
  nlinarith [sq_nonneg (sqrt α-1)]

lemma mp_angular_denominator_pos {α : ℝ} (hα : 0 < α) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 Real.pi) : 0 < 1+α+2*sqrt α*cos x := by
  have hs := sq_sqrt hα.le
  have hc : -1 < cos x := by
    simpa only [cos_pi] using cos_lt_cos_of_nonneg_of_le_pi hx.1.le (le_refl Real.pi) hx.2
  have h := mul_lt_mul_of_pos_left hc (mp_radius_positive hα)
  nlinarith [sq_nonneg (sqrt α-1)]

end InvariantIsing

end

end OAI
