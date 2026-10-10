import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSquareIntegral
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerEnergy

namespace OAI

/-! The exact archimedean constant in the zero-exponent energy integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

theorem cubicWhittakerEnergyMass_zero :
    cubicWhittakerEnergyMass 0=
      Real.Gamma (4/3)*Real.Gamma (2/3)/(32*Real.pi^2) := by
  let c : ℝ := (2*Real.pi)^2
  have hc : 0 < c := by dsimp [c]; positivity
  calc
    _ = (1/8:ℝ)*(∫ v in Ioi (0:ℝ), (2*v^((2:ℝ)-1))*
        (cubicBesselKernel (c*v^(2:ℝ)))^2) := by
      rw [←integral_const_mul]
      unfold cubicWhittakerEnergyMass
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaWhittaker_norm hv]
      norm_num only [mul_zero,zero_sub,Real.rpow_neg_one,Real.rpow_one,Real.rpow_two]
      rw [show (2*Real.pi*v)^2=c*v^2 by dsimp [c]; ring]
      field_simp
      ring
    _ = (1/8:ℝ)*(∫ x in Ioi (0:ℝ), (cubicBesselKernel (c*x))^2) := by
      rw [show (∫ v in Ioi (0:ℝ), (2*v^((2:ℝ)-1))*
          (cubicBesselKernel (c*v^(2:ℝ)))^2)=
          ∫ x in Ioi (0:ℝ), (cubicBesselKernel (c*x))^2 from
        by simpa only [smul_eq_mul] using
          (integral_comp_rpow_Ioi_of_pos (g := fun x : ℝ => (cubicBesselKernel (c*x))^2)
            (by norm_num : (0:ℝ) < 2))]
    _ = (1/8:ℝ)*(c⁻¹*(Real.Gamma (4/3)*Real.Gamma (2/3))) := by
      rw [integral_comp_mul_left_Ioi (fun x : ℝ => (cubicBesselKernel x)^2) 0 hc,mul_zero,
        cubicBesselKernel_sq_integral_value]
      rfl
    _ = _ := by
      dsimp [c]
      field_simp
      ring

end CubicFirstMoment

end

end OAI
