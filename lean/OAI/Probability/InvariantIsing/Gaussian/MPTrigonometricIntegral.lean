import OAI.Probability.InvariantIsing.Gaussian.MPTrigonometricPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The elementary semicircle-over-resolvent integral needed by the MP density. -/
noncomputable section
open Real
namespace InvariantIsing

lemma mp_sine_fraction_identity {a b : ℝ} (hab : |b| < a) (hb : b ≠ 0) (x : ℝ) :
    (sin x)^2/(a+b*cos x) = a/b^2-cos x/b-
      ((a^2-b^2)/b^2)*(1/(a+b*cos x)) := by
  have hd := (mp_cos_denominator_pos hab x).ne'
  field_simp [hb,hd]
  linear_combination b^2*(sin_sq_add_cos_sq x)

theorem mp_integral_sine_fraction {a b : ℝ} (hab : |b| < a) (hb : b ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(a+b*cos x)) =
      Real.pi*(a-sqrt (a^2-b^2))/b^2 := by
  have hc : IntervalIntegrable (fun x : ℝ => cos x/b) MeasureTheory.volume 0 Real.pi :=
    (continuous_cos.div_const b).intervalIntegrable _ _
  have hi : IntervalIntegrable (fun x : ℝ => 1/(a+b*cos x)) MeasureTheory.volume 0 Real.pi :=
    (continuous_const.div (continuous_const.add (continuous_const.mul continuous_cos))
      (fun x => (mp_cos_denominator_pos hab x).ne')).intervalIntegrable _ _
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi, a/b^2-cos x/b-((a^2-b^2)/b^2)*(1/(a+b*cos x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact mp_sine_fraction_identity hab hb x
    _ = Real.pi*(a/b^2)-((a^2-b^2)/b^2)*(Real.pi/sqrt (a^2-b^2)) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub hc) (hi.const_mul _),
        intervalIntegral.integral_sub intervalIntegrable_const hc,
        intervalIntegral.integral_const,intervalIntegral.integral_div,
        integral_cos,intervalIntegral.integral_const_mul,mp_integral_cos_denominator hab]
      simp
    _ = _ := by
      have hs := sqrt_pos.mpr (mp_discriminant_pos hab)
      have hsq := sq_sqrt (mp_discriminant_pos hab).le
      field_simp [hb,hs.ne']
      nlinarith

end InvariantIsing

end

end OAI
