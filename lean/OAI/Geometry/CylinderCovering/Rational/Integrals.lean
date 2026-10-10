import Mathlib

namespace OAI

open intervalIntegral Filter
open scoped Topology

noncomputable section
namespace CylinderCovering.RationalIntegrals

theorem ceiling_integral (α c₀ c₂ : ℝ) :
    (∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), α * (c₀ + c₂ * y ^ 2) * y ^ 2) =
      α * (c₀ / 96 + c₂ / 2560) := by
  have hf : (fun y : ℝ => α * (c₀ + c₂ * y ^ 2) * y ^ 2) =
      (fun y : ℝ => (α * c₀) * y ^ 2 + (α * c₂) * y ^ 4) := by
    funext y
    ring
  rw [hf, integral_add]
  · simp only [integral_const_mul, integral_pow]
    norm_num
    ring
  · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _

theorem limiting_ceiling_integral :
    (∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), ((1 / 16 : ℝ) + y ^ 2) * y ^ 2) =
      (1 / 960 : ℝ) := by
  have h := ceiling_integral 1 (1 / 16) 1
  norm_num at h ⊢
  exact h

theorem limiting_energy_angular_integral :
    (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      ((1 / 16 : ℝ) + z ^ 2 / 4) ^ 2 + (1 / 2 : ℝ) * (z / 2) ^ 2) =
      (17 / 960 : ℝ) := by
  have hf : (fun z : ℝ => ((1 / 16 : ℝ) + z ^ 2 / 4) ^ 2 +
      (1 / 2 : ℝ) * (z / 2) ^ 2) =
      (fun z : ℝ => (1 / 256 : ℝ) + (5 / 32 : ℝ) * z ^ 2 +
        (1 / 16 : ℝ) * z ^ 4) := by
    funext z
    ring
  rw [hf, integral_add, integral_add]
  · simp only [integral_const, integral_const_mul, integral_pow]
    norm_num
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _

theorem limiting_energy_integral :
    (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..(1 / 2 : ℝ), r) *
      (∫ z in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ((1 / 16 : ℝ) + z ^ 2 / 4) ^ 2 + (1 / 2 : ℝ) * (z / 2) ^ 2) =
      (17 / 15360 : ℝ) := by
  rw [limiting_energy_angular_integral, integral_id]
  norm_num

theorem limiting_coefficient_gap :
    (17 / 15360 : ℝ) - (1 / 960 : ℝ) = (1 / 15360 : ℝ) ∧
      0 < (17 / 15360 : ℝ) - (1 / 960 : ℝ) := by
  norm_num

theorem rational_ceiling_coefficient_formula (d : ℝ) :
    (1 / (1 + 2 * d)) *
      (((1 / 2 : ℝ) * (1 / 2 + 2 * d) / (16 * (1 / 2 + d) ^ 2)) / 96 +
        (1 / (4 * (1 / 2 + d) ^ 2)) / 2560) =
    (2 + 5 * d) / (1920 * (1 + 2 * d) ^ 3) := by
  by_cases hd : 1 + 2 * d = 0
  · have he : d = -(1 / 2 : ℝ) := by linarith
    subst d
    norm_num
  · have h : (1 / 2 : ℝ) + d ≠ 0 := by intro he; apply hd; linarith
    field_simp
    ring

theorem rational_ceiling_integral_tendsto :
    Tendsto (fun d : ℝ =>
      ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ),
        (1 / (1 + 2 * d)) *
          (((1 / 2 : ℝ) * (1 / 2 + 2 * d) / (16 * (1 / 2 + d) ^ 2)) +
            (1 / (4 * (1 / 2 + d) ^ 2)) * y ^ 2) * y ^ 2)
      (𝓝 0) (𝓝 (1 / 960 : ℝ)) := by
  simp_rw [ceiling_integral, rational_ceiling_coefficient_formula]
  have h : ContinuousAt (fun d : ℝ =>
      (2 + 5 * d) / (1920 * (1 + 2 * d) ^ 3)) 0 := by
    fun_prop (disch := norm_num)
  convert h.tendsto using 1
  norm_num

theorem rational_ceiling_integral_tendsto_right :
    Tendsto (fun d : ℝ =>
      ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ),
        (1 / (1 + 2 * d)) *
          (((1 / 2 : ℝ) * (1 / 2 + 2 * d) / (16 * (1 / 2 + d) ^ 2)) +
            (1 / (4 * (1 / 2 + d) ^ 2)) * y ^ 2) * y ^ 2)
      (𝓝[Set.Ioi 0] 0) (𝓝 (1 / 960 : ℝ)) :=
  rational_ceiling_integral_tendsto.mono_left nhdsWithin_le_nhds

theorem uncentered_ceiling_integral (c : ℝ) :
    (∫ u in (-c)..c, (c ^ 2 * u ^ 2 / 2 + u ^ 4 / 2)) = (8 / 15 : ℝ) * c ^ 5 := by
  have he : (fun u : ℝ => c ^ 2 * u ^ 2 / 2 + u ^ 4 / 2) =
      (fun u : ℝ => (c ^ 2 / 2) * u ^ 2 + (1 / 2 : ℝ) * u ^ 4) := by
    funext u
    ring
  rw [he, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    norm_num
    ring
  · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _

theorem uncentered_energy_integral (c : ℝ) :
    (1 / 4 : ℝ) * (∫ b in (-c)..c, ((c ^ 2 + b ^ 2) ^ 2 / 4 + b ^ 2)) =
      c ^ 3 / 6 + 7 * c ^ 5 / 30 := by
  have he : (fun b : ℝ => (c ^ 2 + b ^ 2) ^ 2 / 4 + b ^ 2) =
      (fun b : ℝ => c ^ 4 / 4 + (c ^ 2 / 2 + 1) * b ^ 2 + (1 / 4 : ℝ) * b ^ 4) := by
    funext b
    ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow, intervalIntegral.integral_const]
    norm_num
    ring
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _

theorem uncentered_limiting_gap {c : ℝ} (hc : c ^ 2 = (1 / 2 : ℝ)) :
    (1 / 4 : ℝ) * (∫ b in (-c)..c, ((c ^ 2 + b ^ 2) ^ 2 / 4 + b ^ 2)) -
      (∫ u in (-c)..c, (c ^ 2 * u ^ 2 / 2 + u ^ 4 / 2)) = c ^ 3 / 60 := by
  rw [uncentered_energy_integral, uncentered_ceiling_integral]
  have h5 : c ^ 5 = c ^ 3 / 2 := by
    calc c ^ 5 = c ^ 3 * c ^ 2 := by ring
         _ = c ^ 3 / 2 := by rw [hc]; ring
  rw [h5]
  ring

end CylinderCovering.RationalIntegrals

end

end OAI
