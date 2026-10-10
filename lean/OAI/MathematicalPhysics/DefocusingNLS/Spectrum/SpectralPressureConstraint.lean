import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureMeasure
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! A zero limiting step-pressure energy imposes the core constraint. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_step_pressure_constraint (R l b : ℝ) (hb : 0 < b)
    (f : ℝ → ℂ)
    (hf : Integrable (fun r => ‖f r‖^2) (radialPressureMeasure R))
    (hz : (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*‖f r‖^2
      ∂radialPressureMeasure R)=0) :
    f =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0 := by
  have he : (fun r => (Iic l).indicator (fun _ : ℝ => b) r*‖f r‖^2)=
      (Iic l).indicator (fun r => b*‖f r‖^2) := by
    funext r
    by_cases hr : r ∈ Iic l <;> simp [hr]
  rw [he,integral_indicator measurableSet_Iic,integral_const_mul] at hz
  have hzero : (∫ r in Iic l, ‖f r‖^2 ∂radialPressureMeasure R)=0 :=
    (mul_eq_zero.mp hz).resolve_left hb.ne'
  have hae := (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg ‖f r‖)
    hf.integrableOn).mp hzero
  filter_upwards [hae] with r hr
  apply norm_eq_zero.mp
  have hs : ‖f r‖^2=0 := hr
  nlinarith [norm_nonneg (f r)]

end DefocusingNLS

end OAI
