import OAI.NumberTheory.JointDickman.Probability.EndpointFourierMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Paying for a discarded frequency region by endpoint square moments -/

namespace JointDickman
open MeasureTheory

/-- Young's inequality gives the needed two-endpoint estimate without
introducing a separate square root of each Parseval bound. -/
theorem discarded_region_integral_bound {F G H : ℝ → ℂ} {E : Set ℝ} {D : ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Set.Ioc 0 1) (hD : 0 ≤ D)
    (hF : Continuous F) (hG : Continuous G)
    (hH : ∀ θ ∈ E, ‖H θ‖ ≤ D) :
    ‖∫ θ in E, F θ*G θ*H θ‖ ≤
      D/2*((∫ θ in (0 : ℝ)..1, ‖F θ‖^2)+(∫ θ in (0 : ℝ)..1, ‖G θ‖^2)) := by
  let U : ℝ → ℝ := fun θ => D/2*(‖F θ‖^2+‖G θ‖^2)
  have hU : Continuous U := continuous_const.mul ((hF.norm.pow 2).add (hG.norm.pow 2))
  have hU0 (θ : ℝ) : 0 ≤ U θ := by dsimp [U]; positivity
  have hUi : IntegrableOn U (Set.Ioc 0 1) := (hU.intervalIntegrable 0 1).1
  have hUE : IntegrableOn U E := hUi.mono_set hsub
  have hbound (θ : ℝ) (hθ : θ ∈ E) : ‖F θ*G θ*H θ‖ ≤ U θ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (‖F θ‖*‖G θ‖)*D := mul_le_mul_of_nonneg_left (hH θ hθ) (by positivity)
      _ ≤ U θ := by
        have h := sq_nonneg (‖F θ‖-‖G θ‖)
        have hh : ‖F θ‖*‖G θ‖ ≤ (‖F θ‖^2+‖G θ‖^2)/2 := by nlinarith
        have hh' := mul_le_mul_of_nonneg_right hh hD
        dsimp [U]
        nlinarith
  calc
    _ ≤ ∫ θ in E, ‖F θ*G θ*H θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in E, U θ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) hUE
      (by filter_upwards [ae_restrict_mem hE] with θ hθ; exact hbound θ hθ)
    _ ≤ ∫ θ in Set.Ioc 0 1, U θ := setIntegral_mono_set hUi
      (Filter.Eventually.of_forall hU0) (Filter.Eventually.of_forall hsub)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      dsimp [U]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add]
      · exact (hF.norm.pow 2).intervalIntegrable 0 1
      · exact (hG.norm.pow 2).intervalIntegrable 0 1

end JointDickman

end OAI
