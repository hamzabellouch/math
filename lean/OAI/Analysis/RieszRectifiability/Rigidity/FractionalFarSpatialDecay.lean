import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.MeanZeroFarTestEstimate
import OAI.Analysis.RieszRectifiability.Kernel.TranslatedFarTestIntegral

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem far_kernel_mass_times_schwartz_value {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth m C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) (hx : 0 < ‖x‖) :
    ‖(∫ h in closedExterior (0 : Ambient d) (‖x‖ / 2),
      inverseDistancePow (m + 1) 0 h ∂μ) • g x‖ ≤
      (4 * C * 2 ^ m * SchwartzMap.seminorm ℝ (m + 1) 0 g) / ‖x‖ ^ (m + 2) := by
  have hR : 0 < ‖x‖ / 2 := by positivity
  have hC := hgrowth.1
  have hI : 0 ≤ ∫ h in closedExterior (0 : Ambient d) (‖x‖ / 2),
      inverseDistancePow (m + 1) 0 h ∂μ := integral_nonneg fun h => inverseDistancePow_nonneg _ _ _
  have htail := (inverseDistancePow_closedExterior_integrable_and_bound m C μ
    hgrowth 0 (‖x‖ / 2) hR).2
  have hg : ‖g x‖ ≤ SchwartzMap.seminorm ℝ (m + 1) 0 g / ‖x‖ ^ (m + 1) := by
    apply (le_div_iff₀ (pow_pos hx _)).2
    simpa only [mul_comm] using! SchwartzMap.norm_pow_mul_le_seminorm ℝ g (m + 1) x
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hI]
  calc
    _ ≤ (2 * (C * 2 ^ m / (‖x‖ / 2))) *
        (SchwartzMap.seminorm ℝ (m + 1) 0 g / ‖x‖ ^ (m + 1)) :=
      mul_le_mul htail hg (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [pow_add]
      field_simp
      ring

theorem fractionalSchwartz_far_spatial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) (hx : 0 < ‖x‖) :
    ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 (‖x‖ / 2),
      fractionalSchwartzKernel (p + 1) g x h)‖ ≤
      (4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal) * 2 ^ (p + 1) *
          SchwartzMap.seminorm ℝ (p + 2) 0 g +
        (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2) *
          (∫ y : Ambient (p + 1), ‖y‖ * ‖g y‖)) / ‖x‖ ^ (p + 3) := by
  rw [fractionalSchwartz_far_integral_identity p g x (‖x‖ / 2) (by positivity)]
  have hmass := far_kernel_mass_times_schwartz_value (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) g x hx
  have hraw := mean_zero_far_test_integral_bound volume g g.integrable
    (schwartz_first_absolute_moment_integrable g) hmean (p + 1) x hx
  have hn := norm_sub_le
    ((∫ h in closedExterior (0 : Ambient (p + 1)) (‖x‖ / 2),
      inverseDistancePow (p + 1 + 1) 0 h) • g x)
    (∫ y in closedExterior x (‖x‖ / 2), inverseDistancePow (p + 1 + 1) x y • g y)
  simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, ← add_div] using!
    hn.trans (add_le_add hmass hraw)

end

end RieszRectifiability

end OAI
