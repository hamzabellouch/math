import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.DescentDecay

/-- The negative term in the density recurrence dominates the positive term. -/
theorem eventually_exponent_bound (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ S : ℝ in atTop,
      A * S ^ (1 / 4 : ℝ) - c * S ^ (3 / 4 : ℝ) / Real.log S ≤
        -(S ^ (1 / 4 : ℝ)) := by
  have hA1 : 0 < A + 1 := by linarith
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (div_pos hc hA1)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with S hsmall hS
  have hS0 : 0 < S := lt_trans zero_lt_one hS
  have hlog : 0 < Real.log S := Real.log_pos hS
  rw [Real.norm_of_nonneg hlog.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hS0.le _)] at hsmall
  have hprod : (A + 1) * Real.log S ≤ c * S ^ (1 / 2 : ℝ) := by
    calc
      (A + 1) * Real.log S ≤
          (A + 1) * (c / (A + 1) * S ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall hA1.le
      _ = c * S ^ (1 / 2 : ℝ) := by field_simp
  have hp : S ^ (1 / 2 : ℝ) * S ^ (1 / 4 : ℝ) = S ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hS0]
    norm_num
  have hscaled : (A + 1) * S ^ (1 / 4 : ℝ) ≤
      c * S ^ (3 / 4 : ℝ) / Real.log S := by
    apply (le_div_iff₀ hlog).mpr
    calc
      (A + 1) * S ^ (1 / 4 : ℝ) * Real.log S =
          ((A + 1) * Real.log S) * S ^ (1 / 4 : ℝ) := by ring
      _ ≤ (c * S ^ (1 / 2 : ℝ)) * S ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hS0.le _)
      _ = c * S ^ (3 / 4 : ℝ) := by rw [mul_assoc, hp]
  nlinarith

/-- The coarse density bound tends to zero, uniformly in its fixed constants. -/
theorem tendsto_density_envelope_zero (A c K : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hK : 0 ≤ K) :
    Tendsto (fun S : ℝ => K * Real.log S *
      Real.exp (A * S ^ (1 / 4 : ℝ) - c * S ^ (3 / 4 : ℝ) / Real.log S))
      atTop (𝓝 0) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hmajor : Tendsto (fun S : ℝ => K *
      (S ^ (1 / 4 : ℝ) * Real.exp (-(S ^ (1 / 4 : ℝ))))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))
    simpa using h.const_mul K
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with S hS
    exact mul_nonneg (mul_nonneg hK (Real.log_nonneg hS)) (Real.exp_pos _).le
  · filter_upwards [hsmall, eventually_exponent_bound A c hA hc,
      eventually_gt_atTop (1 : ℝ)] with S hsmall hexp hS
    have hS0 : 0 ≤ S := by linarith
    have hlog : 0 ≤ Real.log S := Real.log_nonneg hS.le
    rw [Real.norm_of_nonneg hlog,
      Real.norm_of_nonneg (Real.rpow_nonneg hS0 _), one_mul] at hsmall
    calc
      K * Real.log S * Real.exp
          (A * S ^ (1 / 4 : ℝ) - c * S ^ (3 / 4 : ℝ) / Real.log S) ≤
          K * S ^ (1 / 4 : ℝ) * Real.exp (-(S ^ (1 / 4 : ℝ))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hsmall hK) (Real.exp_le_exp.mpr hexp)
          (Real.exp_pos _).le (mul_nonneg hK (Real.rpow_nonneg hS0 _))
      _ = K * (S ^ (1 / 4 : ℝ) * Real.exp (-(S ^ (1 / 4 : ℝ)))) := by ring

/-- In particular the exceptional density is eventually at most one eighth. -/
theorem eventually_density_envelope_le_eighth (c K r : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop,
      K * Real.log S * Real.exp
        (2 * r * S ^ (1 / 4 : ℝ) - (c / 2) * S ^ (3 / 4 : ℝ) / Real.log S) ≤
          1 / 8 := by
  have h := (tendsto_density_envelope_zero (2 * r) (c / 2) K
    (by positivity) (by positivity) hK).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 8)
  exact h.mono fun _ hS => hS.le

/-- Uniform endgame for the unrolled recurrence with variable depth and scale. -/
theorem eventually_descent_bound_le_eighth (c K r : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ m d : ℝ,
      S / (2 * Real.log S) ≤ m → 0 ≤ d → d ≤ K * Real.log S →
      d * Real.exp (2 * r * S ^ (1 / 4 : ℝ) - c * m * S ^ (-1 / 4 : ℝ)) ≤
        1 / 8 := by
  filter_upwards [eventually_density_envelope_le_eighth c K r hc hK hr,
    eventually_gt_atTop (1 : ℝ)] with S hbound hS
  intro m d hm hd hdK
  have hS0 : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hpower : S * S ^ (-1 / 4 : ℝ) = S ^ (3 / 4 : ℝ) := by
    calc
      S * S ^ (-1 / 4 : ℝ) = S ^ (1 : ℝ) * S ^ (-1 / 4 : ℝ) := by
        rw [Real.rpow_one]
      _ = S ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hS0]; norm_num
  have hm' : (c / 2) * S ^ (3 / 4 : ℝ) / Real.log S ≤
      c * m * S ^ (-1 / 4 : ℝ) := by
    calc
      (c / 2) * S ^ (3 / 4 : ℝ) / Real.log S =
          c * (S / (2 * Real.log S)) * S ^ (-1 / 4 : ℝ) := by
        rw [← hpower]
        ring
      _ ≤ c * m * S ^ (-1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hc.le)
          (Real.rpow_nonneg hS0.le _)
  apply le_trans _ hbound
  exact mul_le_mul hdK (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_pos _).le (mul_nonneg hK hlog.le)

end Problem337.DescentDecay

end

end OAI
