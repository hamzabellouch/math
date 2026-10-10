import OAI.Probability.InvariantIsing.Gaussian.MPAngularShift
import OAI.Probability.InvariantIsing.Gaussian.MarchenkoPasturTransform

namespace OAI

/-! Exact angular Stieltjes transform, with the MP zero atom retained. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_angular_partial_fraction {α t : ℝ} (hα : 0 < α) (ht : 0 < t) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 Real.pi) :
    (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x))) =
      ((sin x)^2/(1+α+2*sqrt α*cos x)-(sin x)^2/(1+α+t+2*sqrt α*cos x))/t := by
  have hd := (mp_angular_denominator_pos hα hx).ne'
  have he := (mp_cos_denominator_pos (mp_shifted_centre_exceeds_radius hα.le ht) x).ne'
  have hs : t+(1+α+2*sqrt α*cos x) = 1+α+t+2*sqrt α*cos x := by ring
  rw [hs]
  field_simp [ht.ne',hd,he]
  ring

theorem mp_angular_transform {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    max (1-α) 0/t+(2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x)))) =
        marchenkoPasturTransform t α := by
  have he : (∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/((1+α+2*sqrt α*cos x)*(t+(1+α+2*sqrt α*cos x)))) =
      ((∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(1+α+2*sqrt α*cos x))-
        ∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(1+α+t+2*sqrt α*cos x))/t := by
    rw [← intervalIntegral.integral_sub (mp_angular_sine_integrable hα) (mp_shifted_sine_integrable hα.le ht),
      ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr_Ioo_of_le pi_pos.le (fun x hx => mp_angular_partial_fraction hα ht hx)
  rw [he,← mul_div_assoc,mul_sub,mp_angular_continuous_mass hα,mp_shifted_angular_integral hα ht]
  have hs : (1+α+t)^2-4*α = (t+α-1)^2+4*t := by ring
  rw [hs]
  have hm := mp_total_mass α
  unfold marchenkoPasturTransform
  field_simp
  nlinarith

end InvariantIsing

end

end OAI
