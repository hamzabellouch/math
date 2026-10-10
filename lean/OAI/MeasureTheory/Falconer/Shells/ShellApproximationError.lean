import OAI.MeasureTheory.Falconer.Shells.ShellMultipliers

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem norm_square_of_error {z w : ℂ} {e : ℝ} (he : 0 ≤ e) (h : ‖z-w‖ ≤ e) :
    ‖z‖^2 ≤ 2*‖w‖^2+2*e^2 := by
  have hn : ‖z‖ ≤ ‖w‖+e := by
    calc
      _ = ‖(z-w)+w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z-w‖+‖w‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  nlinarith [sq_nonneg (‖w‖-e),
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) he)).2 hn]

theorem shell_square_approximation (μ : Measure ℝ) [IsFiniteMeasure μ]
    (F G : ℝ → ℂ) (hG : Measurable G)
    (hiF : Integrable (fun r => ‖F r‖^2) μ) {e : ℝ} (he : 0 ≤ e)
    (herr : ∀ᵐ r ∂μ, ‖F r-G r‖ ≤ e) :
    Integrable (fun r => ‖G r‖^2) μ ∧
      (∫ r, ‖F r‖^2 ∂μ) ≤ 2*(∫ r, ‖G r‖^2 ∂μ)+2*e^2*μ.real Set.univ := by
  have hGi : Integrable (fun r => ‖G r‖^2) μ := by
    apply ((hiF.const_mul 2).add (integrable_const (2*e^2))).mono'
      (hG.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [herr] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact norm_square_of_error he (by simpa only [norm_sub_rev] using hr)
  refine ⟨hGi,?_⟩
  calc
    _ ≤ ∫ r, 2*‖G r‖^2+2*e^2 ∂μ :=
      integral_mono_ae hiF ((hGi.const_mul 2).add (integrable_const (2*e^2)))
        (herr.mono (fun r hr => norm_square_of_error he hr))
    _ = _ := by
      rw [integral_add (hGi.const_mul 2) (integrable_const (2*e^2)),integral_const_mul,integral_const]
      simp only [smul_eq_mul]
      ring

end PlanarFalconer

end OAI
