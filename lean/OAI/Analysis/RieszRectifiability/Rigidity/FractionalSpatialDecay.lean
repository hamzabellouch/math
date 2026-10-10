import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.FinitePairingCancellation
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalNearSpatialDecay
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalFarSpatialDecay
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzContinuity

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

def fractionalSchwartzDecaySize (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) : ℝ :=
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) * SchwartzMap.seminorm ℝ (p + 4) 2 g +
    (4 * C * 2 ^ (p + 1) * SchwartzMap.seminorm ℝ (p + 2) 0 g +
      (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2) *
        (∫ y : Ambient (p + 1), ‖y‖ * ‖g y‖))

theorem fractionalSchwartzDecaySize_nonneg (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    0 ≤ fractionalSchwartzDecaySize p g := by
  unfold fractionalSchwartzDecaySize
  positivity

theorem fractionalSchwartzTest_spatial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) (hx : 0 < ‖x‖) :
    ‖fractionalSchwartzTest p g x‖ ≤ fractionalSchwartzDecaySize p g / ‖x‖ ^ (p + 3) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let N := 4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
    SchwartzMap.seminorm ℝ (p + 4) 2 g
  let R := ‖x‖ / 2
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hsplit : (∫ h, K h) = (∫ h in ball 0 R, K h) +
      (∫ h in closedExterior 0 R, K h) := by
    rw [closedExterior_eq_compl_ball]
    exact (integral_add_compl measurableSet_ball hi).symm
  have hnear : ‖(-1 / 2 : ℝ) • (∫ h in ball 0 R, K h)‖ ≤ N / ‖x‖ ^ (p + 3) := by
    calc
      _ ≤ ‖∫ h in ball 0 R, K h‖ := by
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        norm_num
        linarith [norm_nonneg (∫ h in ball 0 R, K h)]
      _ ≤ ∫ h in ball 0 R, ‖K h‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ h in closedBall 0 R, ‖K h‖ :=
        integral_mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
          (Filter.Eventually.of_forall fun h => norm_nonneg (K h)) hi.norm.restrict
      _ ≤ _ := fractionalSchwartzKernel_near_spatial_decay p C volume
        (volume_global_upper_growth (p + 1)) g x hx
  have hfar := fractionalSchwartz_far_spatial_decay p g hmean x hx
  have he : fractionalSchwartzTest p g x =
      (-1 / 2 : ℝ) • (∫ h in ball 0 R, K h) +
      (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h) := by
    change (-1 / 2 : ℝ) • (∫ h, K h) = _
    rw [hsplit]
    exact smul_add (-1 / 2 : ℝ) _ _
  rw [he]
  calc
    _ ≤ ‖(-1 / 2 : ℝ) • (∫ h in ball 0 R, K h)‖ +
        ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h)‖ := norm_add_le _ _
    _ ≤ _ := by
      have hh := add_le_add hnear hfar
      simpa only [← add_div, N, C, fractionalSchwartzDecaySize] using! hh

end

end RieszRectifiability

end OAI
