import OAI.Probability.InvariantIsing.Gaussian.MPTrigonometricCritical
import OAI.Probability.InvariantIsing.Gaussian.MPEdgeArithmetic

namespace OAI

/-! Normalization of the continuous part of the MP law in angular coordinates. -/
noncomputable section
open Real
namespace InvariantIsing

theorem mp_angular_continuous_mass {α : ℝ} (hα : 0 < α) :
    (2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/(1+α+2*sqrt α*cos x)) = min 1 α := by
  by_cases he : α = 1
  · subst α
    have h := mp_integral_sine_fraction_critical (b := 2) (by norm_num)
    norm_num at h ⊢
    rw [h]
    field_simp
  · have hab := mp_centre_exceeds_radius hα.le he
    have hb := (mp_radius_positive hα).ne'
    rw [mp_integral_sine_fraction hab hb,mp_centre_radius_sqrt hα.le]
    have hs : (2*sqrt α)^2 = 4*α := by nlinarith [sq_sqrt hα.le]
    rw [hs]
    calc
      _ = (1+α-|α-1|)/2 := by field_simp; ring
      _ = _ := mp_continuous_mass α

theorem mp_angular_total_mass {α : ℝ} (hα : 0 < α) :
    max (1-α) 0+(2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/(1+α+2*sqrt α*cos x)) = 1 := by
  rw [mp_angular_continuous_mass hα]
  exact mp_total_mass α

end InvariantIsing

end

end OAI
