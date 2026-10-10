import OAI.Geometry.CylinderCovering.Convexity.OrthonormalHeightComparisonDefinitions
import OAI.Geometry.CylinderCovering.Radial.JointFailure

namespace OAI

noncomputable section
namespace CylinderCovering.OrthonormalHeight

lemma k_pos : 0 < k := by unfold k; positivity
lemma k_ne : k ≠ 0 := ne_of_gt k_pos
lemma k_sq : k ^ 2 = (1 / 2 : ℝ) := by
  unfold k
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma upperHeight_scale (τ y z q : ℝ) :
    k * upperHeight τ y z q = 1 - k * z + (k * τ) * y * q := by
  unfold upperHeight
  field_simp [k_ne]

lemma lowerHeight_scale (τ x z p : ℝ) :
    k * lowerHeight τ x z p = 1 + k * z - (k * τ) * x * p := by
  unfold lowerHeight
  field_simp [k_ne]

lemma cap_dictionary (τ r : ℝ) :
    k * cap τ r = RadialCaps.cubicCap 20 (k * τ) r := by
  have hcube : 20 * k ^ 3 = 10 * k := by
    calc
      20 * k ^ 3 = 20 * k * k ^ 2 := by ring
      _ = 10 * k := by rw [k_sq]; ring
  unfold cap RadialCaps.cubicCap
  have hc : k * (1 / k) = 1 := by field_simp [k_ne]
  calc
    k * (1 / k + τ ^ 2 * k * RadialCaps.H r + 10 * τ ^ 3) =
        1 + (k * τ) ^ 2 * RadialCaps.H r + 10 * k * τ ^ 3 := by
      linear_combination hc
    _ = 1 + (k * τ) ^ 2 * RadialCaps.H r + 20 * (k * τ) ^ 3 := by
      linear_combination -τ ^ 3 * hcube

theorem error_bound : ErrorStatement := by
  intro τ x y z p q hτ hx hy hp hq hroot hU hL
  obtain ⟨hrootq, hrootp⟩ := hroot
  have hu : 1 < 1 - k * z + (k * τ) * y * q := by
    have hh := mul_lt_mul_of_pos_left hU k_pos
    rw [upperHeight_scale] at hh
    have hc : k * (1 / k) = 1 := by field_simp [k_ne]
    rwa [hc] at hh
  have hl : 1 < 1 + k * z - (k * τ) * x * p := by
    have hh := mul_lt_mul_of_pos_left hL k_pos
    rw [lowerHeight_scale] at hh
    have hc : k * (1 / k) = 1 := by field_simp [k_ne]
    rwa [hc] at hh
  have h := RadialCapCoverage.joint_failure_estimate (mul_pos k_pos hτ)
    hy hx hp hq hrootq hrootp hu hl
  have hh : k * (τ * (y * q - x * p)) ≤
      k * (k * τ ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * k ^ 2 * τ ^ 3) := by
    convert h.2.2.2.2 using 1 <;> first | rfl | ring
  exact (mul_le_mul_iff_right₀ k_pos).mp hh

theorem cubic_coverage : CoverageStatement := by
  intro τ x y z hτ hx hy
  have hc := RadialCapCoverage.padding_coverage
    (R := fun r => k * cap τ r) (b := fun _ => 20 * (k * τ)) (mul_pos k_pos hτ)
    (by
      intro r hr
      rw [cap_dictionary]
      unfold RadialCaps.cubicCap
      ring)
    (by intro r hr; positivity [k_pos])
    (by intro p hp q hq; nlinarith only [mul_pos k_pos hτ]) hy hx
  rcases hc with hU | hL
  · obtain ⟨q, ρ, hq, hρ, hR, hrep, hz⟩ := hU
    left
    refine ⟨q, ρ / k, hq, div_nonneg hρ k_pos.le, ?_, ?_, ?_⟩
    · apply (div_le_iff₀ k_pos).2
      simpa only [mul_comm] using hR
    · rw [hrep]
      field_simp [k_ne]
    · apply (mul_left_cancel₀ k_ne)
      calc
        k * z = 1 - ρ + (k * τ) * y * q := hz
        _ = k * (1 / k - ρ / k + τ * y * q) := by field_simp [k_ne]
  · obtain ⟨p, σ, hp, hσ, hR, hrep, hz⟩ := hL
    right
    refine ⟨p, σ / k, hp, div_nonneg hσ k_pos.le, ?_, ?_, ?_⟩
    · apply (div_le_iff₀ k_pos).2
      simpa only [mul_comm] using hR
    · rw [hrep]
      field_simp [k_ne]
    · apply (mul_left_cancel₀ k_ne)
      calc
        k * z = -1 + σ + (k * τ) * x * p := hz
        _ = k * (-1 / k + σ / k + τ * x * p) := by field_simp [k_ne]

theorem orthonormal_height_comparison : Statement := ⟨error_bound, cubic_coverage⟩

end CylinderCovering.OrthonormalHeight

end

end OAI
