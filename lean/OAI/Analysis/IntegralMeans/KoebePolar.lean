import OAI.Analysis.IntegralMeans.KoebeCone
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace OAI

noncomputable section

namespace Brennan.Sharp

lemma sector_cos_lower {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    (1 : ℝ) / 2 ≤ Real.cos θ := by
  have habs : |θ| ≤ Real.pi / 3 :=
    (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) habs
  simpa only [Real.cos_pi_div_three, Real.cos_abs] using h

lemma polar_cone_data {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    ‖Complex.polarCoord.symm (r, θ)‖ = r ∧
      ‖Complex.polarCoord.symm (r, θ)‖ / 2 ≤
        (Complex.polarCoord.symm (r, θ)).re := by
  have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
    simpa only [abs_of_pos hr] using Complex.norm_polarCoord_symm (r, θ)
  refine ⟨hn, ?_⟩
  have hre : (Complex.polarCoord.symm (r, θ)).re = r * Real.cos θ := by
    rw [Complex.polarCoord_symm_apply]
    simp [Complex.cos_ofReal_re]
  rw [hn, hre]
  have hmul := mul_le_mul_of_nonneg_left (sector_cos_lower hθ) hr.le
  nlinarith

lemma polar_left_mem_disk {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    -1 + Complex.polarCoord.symm (r, θ) ∈ disk := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  exact left_cone_mem_disk (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc

lemma polar_right_mem_disk {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    1 - Complex.polarCoord.symm (r, θ) ∈ disk := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  exact right_cone_mem_disk (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc

lemma koebe_polar_left_lower {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    1 / r ^ 2 ≤ ‖deriv koebeMap (-1 + Complex.polarCoord.symm (r, θ))‖ ^ (-2 : ℝ) := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  have h := koebe_left_cone_lower (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc
  simpa only [hn] using h

lemma koebe_polar_right_lower {r θ : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 3)) (Real.pi / 3)) :
    1 / r ^ 2 ≤ ‖deriv koebeMap (1 - Complex.polarCoord.symm (r, θ))‖ ^ (2 / 3 : ℝ) := by
  obtain ⟨hn, hc⟩ := polar_cone_data hr.1 hθ
  have h := koebe_right_cone_lower (w := Complex.polarCoord.symm (r, θ)) (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2) hc
  simpa only [hn] using h

end Brennan.Sharp

end

end OAI
