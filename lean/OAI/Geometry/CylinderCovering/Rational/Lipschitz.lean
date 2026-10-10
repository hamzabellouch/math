import OAI.Geometry.CylinderCovering.Rational.Field

namespace OAI

noncomputable section

namespace SlopeRational

theorem matrixCLM_norm_le (a b c d : ℝ) :
    ‖matrixCLM a b c d‖ ≤ |a| + |b| + |c| + |d| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hw0 : |w 0| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w 0
  have hw1 : |w 1| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w 1
  have hfirst : |a * w 0 + b * w 1| ≤ (|a| + |b|) * ‖w‖ := by
    calc
      _ ≤ |a * w 0| + |b * w 1| := abs_add_le _ _
      _ = |a| * |w 0| + |b| * |w 1| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * ‖w‖ + |b| * ‖w‖ := by gcongr
      _ = _ := by ring
  have hsecond : |c * w 0 + d * w 1| ≤ (|c| + |d|) * ‖w‖ := by
    calc
      _ ≤ |c * w 0| + |d * w 1| := abs_add_le _ _
      _ = |c| * |w 0| + |d| * |w 1| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * ‖w‖ + |d| * ‖w‖ := by gcongr
      _ = _ := by ring
  rw [matrixCLM_apply]
  have hn := plane_norm_le_sum (vec2 (a * w 0 + b * w 1) (c * w 0 + d * w 1))
  simp only [vec2_zero, vec2_one] at hn
  nlinarith

theorem derivative_entry_bounds {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    |z 0 / (2 * (radius (z 1) + d) ^ 2)| ≤ 1 / (2 * d) ∧
      |(d ^ 2 - 4 * z 0 ^ 2) / (8 * (radius (z 1) + d) ^ 3)| ≤ 1 / (2 * d) ∧
      |1 / (2 * (radius (z 1) + d))| ≤ 1 / (2 * d) := by
  let R := radius (z 1)
  let D := R + d
  have hR : 0 ≤ R := radius_nonneg_of_mem_wedge hz
  have hD : 0 < D := add_pos_of_nonneg_of_pos hR hd
  have hdD : d ≤ D := by dsimp [D]; linarith
  have hw : 2 * |z 0| ≤ R := hz
  have hyD : |z 0| ≤ D := by dsimp [D]; linarith [abs_nonneg (z 0)]
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2 * |z 0|) hw
  have hy2 : 4 * (z 0) ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs (z 0)]
  have hnum : |d ^ 2 - 4 * z 0 ^ 2| ≤ D ^ 2 := by
    apply abs_le.mpr
    dsimp [D]
    constructor <;> nlinarith [mul_nonneg hR hd.le, sq_nonneg d, sq_nonneg (z 0)]
  have h2d : 0 < 2 * d := by positivity
  have h2D : 0 < 2 * D := by positivity
  have h2D2 : 0 < 2 * D ^ 2 := by positivity
  have h8D3 : 0 < 8 * D ^ 3 := by positivity
  change |z 0 / (2 * D ^ 2)| ≤ 1 / (2 * d) ∧
    |(d ^ 2 - 4 * z 0 ^ 2) / (8 * D ^ 3)| ≤ 1 / (2 * d) ∧
    |1 / (2 * D)| ≤ 1 / (2 * d)
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos h2D2]
    apply (div_le_div_iff₀ h2D2 h2d).mpr
    have hp := mul_le_mul hyD hdD hd.le hD.le
    nlinarith
  · rw [abs_div, abs_of_pos h8D3]
    apply (div_le_div_iff₀ h8D3 h2d).mpr
    have hp := mul_le_mul hnum hdD hd.le (sq_nonneg D)
    have hD3 : 0 ≤ D ^ 3 := by positivity
    nlinarith
  · rw [abs_of_pos (div_pos (by norm_num) h2D)]
    apply (div_le_div_iff₀ h2D h2d).mpr
    linarith

theorem field_derivative_norm_bound {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    ‖fderiv ℝ (field d) z‖ ≤ 2 / d := by
  rw [field_fderiv d (denominator_pos_of_mem_wedge hd hz).ne']
  obtain ⟨hdiag, hoff, hlo⟩ := derivative_entry_bounds hd hz
  have hn := matrixCLM_norm_le
    (-z 0 / (2 * (radius (z 1) + d) ^ 2))
    ((d ^ 2 - 4 * z 0 ^ 2) / (8 * (radius (z 1) + d) ^ 3))
    (1 / (2 * (radius (z 1) + d)))
    (z 0 / (2 * (radius (z 1) + d) ^ 2))
  rw [neg_div, abs_neg] at hn
  rw [neg_div]
  have he : 4 * (1 / (2 * d)) = 2 / d := by ring
  linarith

theorem wedge_convex : Convex ℝ wedge := by
  intro x hx y hy a b ha hb hab
  change 2 * |a * x 0 + b * y 0| ≤ radius (a * x 1 + b * y 1)
  have hx' : 2 * |x 0| ≤ radius (x 1) := hx
  have hy' : 2 * |y 0| ≤ radius (y 1) := hy
  calc
    2 * |a * x 0 + b * y 0| ≤ 2 * (a * |x 0| + b * |y 0|) := by
      have h := abs_add_le (a * x 0) (b * y 0)
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
      linarith
    _ ≤ a * radius (x 1) + b * radius (y 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]
    _ = _ := by unfold radius; nlinarith

theorem field_lipschitzOn_wedge {d : ℝ} (hd : 0 < d) :
    LipschitzOnWith ⟨2 / d, by positivity⟩ (field d) wedge := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun z hz => (field_contDiffAt d (denominator_pos_of_mem_wedge hd hz).ne').differentiableAt
      (by norm_num)) ?_ wedge_convex
  intro z hz
  exact field_derivative_norm_bound hd hz

end SlopeRational

end

end OAI
