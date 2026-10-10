import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLogHeight
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! The radial L2 mass and energy after logarithmic height conjugation.
The measure factors are exactly those of hyperbolic three-space. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaLogLift_mass_integrand (f : ℝ → ℂ) {v : ℝ} (hv : 0<v) :
    ‖cubicThetaLogLift f v‖^2/v^3=v⁻¹*‖f (Real.log v)‖^2 := by
  rw [cubicThetaLogLift,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  field_simp

theorem cubicThetaLogLift_mass (f : ℝ → ℂ) :
    (∫ v in Ioi (0:ℝ), ‖cubicThetaLogLift f v‖^2/v^3)=
      ∫ t : ℝ, ‖f t‖^2 := by
  calc
    _ = ∫ v in Ioi (0:ℝ), v⁻¹*‖f (Real.log v)‖^2 :=
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => cubicThetaLogLift_mass_integrand f hv)
    _ = _ := integral_comp_log_Ioi_zero (fun t : ℝ => ‖f t‖^2)

theorem cubicThetaLogLift_mass_integrable_iff (f : ℝ → ℂ) :
    IntegrableOn (fun v : ℝ => ‖cubicThetaLogLift f v‖^2/v^3) (Ioi 0) ↔
      Integrable (fun t : ℝ => ‖f t‖^2) := by
  have he : (fun v : ℝ => ‖cubicThetaLogLift f v‖^2/v^3) =ᵐ[volume.restrict (Ioi 0)]
      (fun v : ℝ => v⁻¹*‖f (Real.log v)‖^2) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => cubicThetaLogLift_mass_integrand f hv)
  exact (integrable_congr he).trans (integrableOn_comp_log_Ioi_zero (fun t : ℝ => ‖f t‖^2))

theorem cubicThetaLogLift_energy {f : ℝ → ℂ} (hf : Differentiable ℝ f) :
    (∫ v in Ioi (0:ℝ), ‖deriv (cubicThetaLogLift f) v‖^2/v)=
      ∫ t : ℝ, ‖f t+deriv f t‖^2 := by
  calc
    _ = ∫ v in Ioi (0:ℝ), v⁻¹*‖f (Real.log v)+deriv f (Real.log v)‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change ‖deriv (cubicThetaLogLift f) v‖^2/v=
        v⁻¹*‖f (Real.log v)+deriv f (Real.log v)‖^2
      rw [(cubicThetaLogLift_hasDerivAt hf hv).deriv]
      ring
    _ = _ := integral_comp_log_Ioi_zero (fun t : ℝ => ‖f t+deriv f t‖^2)

end CubicFirstMoment

end

end OAI
