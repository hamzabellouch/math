import OAI.MeasureTheory.Falconer.Angular.ProjectionAngularMoment

namespace OAI

/-! Normalized projection kernels, including their diagonal convention. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def directionalProjectionKernel {d : ℕ} (s : ℝ) (w : Sphere d)
    (v : Space d) : ℝ≥0∞ :=
  if v = 0 then 1 else
    (ENNReal.ofReal ‖perpendicularPart (w : Space d) (‖v‖⁻¹ • v)‖)^(-s)

theorem directionalProjectionKernel_measurable {d : ℕ} (s : ℝ) :
    Measurable (fun p : Sphere d × Space d => directionalProjectionKernel s p.1 p.2) := by
  unfold directionalProjectionKernel perpendicularPart
  apply Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
  · exact measurable_const
  · fun_prop

theorem projection_kernel_factor {d : ℕ} (s : ℝ)
    (w : Sphere d) (v : Space d) :
    (ENNReal.ofReal ‖perpendicularPart (w : Space d) v‖)^(-s) =
      (ENNReal.ofReal ‖v‖)^(-s) * directionalProjectionKernel s w v := by
  by_cases hv : v = 0
  · subst v
    simp [directionalProjectionKernel, perpendicularPart]
  · have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hnorm : ‖perpendicularPart (w : Space d) v‖ =
        ‖v‖ * ‖perpendicularPart (w : Space d) (‖v‖⁻¹ • v)‖ := by
      rw [perpendicularPart_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp)]
      field_simp
    rw [directionalProjectionKernel, ite_eq_right_iff.mpr (fun h => (hv h).elim), hnorm,
      ENNReal.ofReal_mul hvp.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]

theorem directionalProjectionKernel_rpow {d : ℕ} (s r : ℝ) (w : Sphere d) (v : Space d) :
    directionalProjectionKernel s w v ^ r = directionalProjectionKernel (s*r) w v := by
  by_cases hv : v = 0
  · simp [directionalProjectionKernel, hv]
  · simp only [directionalProjectionKernel, hv, ite_false, ← ENNReal.rpow_mul]
    congr 1
    ring

theorem directionalProjectionKernel_angular_bound (n : ℕ) {s : ℝ}
    (hs : 0 < s) (hsn : s < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ v : Space (n+1),
      (∫⁻ w : Sphere (n+1), directionalProjectionKernel s w v ∂sphereMeasure (n+1)) ≤ C := by
  obtain ⟨B, hB, hb⟩ := unit_projection_angular_bound n hs hsn
  refine ⟨B + sphereMeasure (n+1) univ,
    ENNReal.add_lt_top.mpr ⟨hB, measure_lt_top _ _⟩, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp only [directionalProjectionKernel, hv, ite_true, lintegral_const, one_mul]
    exact le_add_left le_rfl
  · have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    simp only [directionalProjectionKernel, hv, ite_false]
    exact (hb _ hu).trans (le_add_right le_rfl)

end Falconer

end OAI
