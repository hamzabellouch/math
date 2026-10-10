import OAI.Probability.InvariantIsing.Gaussian.MPAngularIntegrability

namespace OAI

/-! The elementary shifted angular integral for the MP Stieltjes transform. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_shifted_centre_exceeds_radius {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    |2*sqrt α| < 1+α+t := by
  have hs := sq_sqrt hα
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (sqrt α-1)]

lemma mp_shifted_sine_integrable {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    IntervalIntegrable (fun x => (sin x)^2/(1+α+t+2*sqrt α*cos x)) volume 0 Real.pi :=
  ((continuous_sin.pow 2).div (continuous_const.add (continuous_const.mul continuous_cos))
    (fun x => (mp_cos_denominator_pos (mp_shifted_centre_exceeds_radius hα ht) x).ne')).intervalIntegrable _ _

lemma mp_shifted_angular_integral {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    (2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/(1+α+t+2*sqrt α*cos x)) =
        (1+α+t-sqrt ((1+α+t)^2-4*α))/2 := by
  have hab := mp_shifted_centre_exceeds_radius hα.le ht
  rw [mp_integral_sine_fraction hab (mp_radius_positive hα).ne']
  have hs : (2*sqrt α)^2 = 4*α := by nlinarith [sq_sqrt hα.le]
  rw [hs]
  field_simp
  ring

end InvariantIsing

end

end OAI
