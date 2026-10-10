import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalWeightedDecay
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalTruncatedTests

namespace OAI

/-!
# Spatial decay of truncated fractional tests

For a mean-zero Schwartz function, split the truncated fractional kernel integral
at half the observation-point norm. The local second-difference estimate and the
far-field cancellation bound give decay uniform in smaller truncation radii.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem fractionalSchwartzTruncatedTest_spatial_decay (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0)
    (x : Ambient (p + 1)) (hx : 0 < ‖x‖) (hε : ε ≤ ‖x‖ / 2) :
    ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤
      fractionalSchwartzDecaySize p g / ‖x‖ ^ (p + 3) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let N := 4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
    SchwartzMap.seminorm ℝ (p + 4) 2 g
  let R := ‖x‖ / 2
  let E : Set (Ambient (p + 1)) := closedExterior 0 ε
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have he : E \ ball 0 R = closedExterior 0 R := by
    rw [sdiff_eq, ← closedExterior_eq_compl_ball]
    apply inter_eq_right.mpr
    intro h hh
    exact hε.trans hh
  have hsplit : (∫ h in E, K h) = (∫ h in E ∩ ball 0 R, K h) +
      (∫ h in closedExterior 0 R, K h) := by
    have hh := integral_inter_add_sdiff (t := ball 0 R) measurableSet_ball (hi.restrict (s := E))
    rw [he] at hh
    exact hh.symm
  have hnear : ‖(-1 / 2 : ℝ) • (∫ h in E ∩ ball 0 R, K h)‖ ≤ N / ‖x‖ ^ (p + 3) := by
    calc
      _ ≤ ‖∫ h in E ∩ ball 0 R, K h‖ := by
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        norm_num
        linarith [norm_nonneg (∫ h in E ∩ ball 0 R, K h)]
      _ ≤ ∫ h in E ∩ ball 0 R, ‖K h‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ h in closedBall 0 R, ‖K h‖ :=
        integral_mono_measure
          (Measure.restrict_mono (inter_subset_right.trans ball_subset_closedBall) le_rfl)
          (Filter.Eventually.of_forall fun h => norm_nonneg (K h)) hi.norm.restrict
      _ ≤ _ := fractionalSchwartzKernel_near_spatial_decay p C volume
        (volume_global_upper_growth (p + 1)) g x hx
  have hfar := fractionalSchwartz_far_spatial_decay p g hmean x hx
  have hform : fractionalSchwartzTruncatedTest p ε g x =
      (-1 / 2 : ℝ) • (∫ h in E ∩ ball 0 R, K h) +
      (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h) := by
    change (-1 / 2 : ℝ) • (∫ h in E, K h) = _
    rw [hsplit]
    exact smul_add (-1 / 2 : ℝ) _ _
  rw [hform]
  calc
    _ ≤ ‖(-1 / 2 : ℝ) • (∫ h in E ∩ ball 0 R, K h)‖ +
        ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h)‖ := norm_add_le _ _
    _ ≤ _ := by
      simpa only [← add_div, N, C, fractionalSchwartzDecaySize] using! add_le_add hnear hfar

theorem fractionalSchwartzTruncatedTest_polynomial_decay (p : ℕ) (ε : ℝ) (hε : ε ≤ 1)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤
      (3 ^ (p + 3) * (fractionalSchwartzUniformSize p g + fractionalSchwartzDecaySize p g)) *
        polynomialDecay (p + 3) x := by
  let U := fractionalSchwartzUniformSize p g
  let D := fractionalSchwartzDecaySize p g
  have hU : 0 ≤ U := by dsimp [U, fractionalSchwartzUniformSize]; positivity
  have hD : 0 ≤ D := fractionalSchwartzDecaySize_nonneg p g
  have hu : ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤ U :=
    fractionalSchwartzTruncatedTest_uniform_bound p ε g x
  rw [polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖x‖) (p + 3))).2
  by_cases hx : 2 ≤ ‖x‖
  · have hp : 0 < ‖x‖ := by linarith
    have hd := fractionalSchwartzTruncatedTest_spatial_decay p ε g hmean x hp (by linarith)
    have hb : (1 + ‖x‖) ^ (p + 3) ≤ (2 * ‖x‖) ^ (p + 3) :=
      pow_le_pow_left₀ (by positivity) (by linarith) (p + 3)
    calc
      _ ≤ (D / ‖x‖ ^ (p + 3)) * (2 * ‖x‖) ^ (p + 3) :=
        mul_le_mul hd hb (by positivity) (div_nonneg hD (by positivity))
      _ = 2 ^ (p + 3) * D := by rw [mul_pow]; field_simp
      _ ≤ 3 ^ (p + 3) * (U + D) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num : (2 : ℝ) ≤ 3) (p + 3)) (by linarith) hD (by positivity)
  · have hb : (1 + ‖x‖) ^ (p + 3) ≤ (3 : ℝ) ^ (p + 3) :=
      pow_le_pow_left₀ (by positivity) (by linarith) (p + 3)
    calc
      _ ≤ U * 3 ^ (p + 3) := mul_le_mul hu hb (by positivity) hU
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (by linarith : U ≤ U + D)
          (by positivity : 0 ≤ (3 : ℝ) ^ (p + 3))
        simpa only [mul_comm] using! hh

end

end RieszRectifiability

end OAI
