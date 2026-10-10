import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.DyadicExcessSchedule

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

def propagationScale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

def propagationHorizon (j : ℕ) : ℕ := 2 * j + 3

def propagationTestRadius (j : ℕ) : ℝ := 8 * (2 : ℝ) ^ propagationHorizon j

theorem propagationScale_pos (j : ℕ) : 0 < propagationScale j := by
  unfold propagationScale
  positivity

theorem propagationScale_tendsto_zero : Tendsto propagationScale atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)

theorem propagationHorizon_tendsto_atTop : Tendsto propagationHorizon atTop atTop := by
  have h : StrictMono propagationHorizon := by
    intro i j hij
    dsimp [propagationHorizon]
    omega
  exact h.tendsto_atTop

theorem propagationTestRadius_tendsto_atTop : Tendsto propagationTestRadius atTop atTop := by
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      propagationHorizon_tendsto_atTop)

theorem propagation_horizon_product_tendsto_zero (b : ℝ) (hb : b ^ 2 < 2) :
    Tendsto (fun j => propagationScale j * b ^ propagationHorizon j) atTop (𝓝 0) :=
  dyadic_excess_horizon_tendsto_zero b hb

theorem propagation_last_error_tendsto_zero :
    Tendsto (fun j => ((2 : ℝ) ^ propagationHorizon j)⁻¹ / propagationScale j) atTop (𝓝 0) := by
  simpa only [one_mul] using! normalized_last_radius_dyadic_tendsto 1 zero_lt_one

end

end RieszRectifiability

end OAI
