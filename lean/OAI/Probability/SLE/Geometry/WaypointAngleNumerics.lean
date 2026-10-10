import OAI.Probability.SLE.Geometry.PublishedConformalExitLaw

namespace OAI

/-! The quantitative conversion from the two half-plane exit-arc
probabilities to the exact sine normalization used by guide compactness. -/

noncomputable section
open Set
open scoped ENNReal

namespace SLEExactGauge.CrosscutSides

theorem sine_lower_bound_of_two_arc_bounds
    {θ q : ℝ} (hθ : θ ∈ Icc 0 Real.pi)
    (hl : q ≤ θ / Real.pi) (hr : q ≤ 1 - θ / Real.pi) :
    2 * q ≤ Real.sin θ := by
  have hl' := (le_div_iff₀ Real.pi_pos).mp hl
  have hr' : q * Real.pi ≤ Real.pi - θ := by
    have hh := mul_le_mul_of_nonneg_right hr Real.pi_pos.le
    have he : (1 - θ / Real.pi) * Real.pi = Real.pi - θ := by
      field_simp
    rw [he] at hh
    exact hh
  by_cases hh : θ ≤ Real.pi / 2
  · calc
      2 * q ≤ 2 / Real.pi * θ := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ Real.pi_pos).mpr
        nlinarith
      _ ≤ Real.sin θ := Real.mul_le_sin hθ.1 hh
  · calc
      2 * q ≤ 2 / Real.pi * (Real.pi - θ) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ Real.pi_pos).mpr
        nlinarith
      _ ≤ Real.sin (Real.pi - θ) :=
        Real.mul_le_sin (by linarith [hθ.2]) (by linarith)
      _ = Real.sin θ := Real.sin_pi_sub θ

theorem positive_angle_of_two_exit_probability_bounds
    {q : ℝ≥0∞} (hq : 0 < q) {w : ℂ} (hw : 0 < w.im)
    (hl : q ≤ ENNReal.ofReal (w.arg / Real.pi))
    (hr : q ≤ ENNReal.ofReal (1 - w.arg / Real.pi)) :
    0 < q.toReal ∧ 2 * q.toReal ≤ w.im / ‖w‖ := by
  have hθ : w.arg ∈ Icc (0 : ℝ) Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr hw.le, Complex.arg_le_pi w⟩
  have hfin : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl
  have hlreal : q.toReal ≤ w.arg / Real.pi := by
    simpa only [ENNReal.toReal_ofReal (div_nonneg hθ.1 Real.pi_pos.le)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  have hrnonneg : 0 ≤ 1 - w.arg / Real.pi :=
    sub_nonneg.mpr ((div_le_one Real.pi_pos).mpr hθ.2)
  have hrreal : q.toReal ≤ 1 - w.arg / Real.pi := by
    simpa only [ENNReal.toReal_ofReal hrnonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
  refine ⟨ENNReal.toReal_pos hq.ne' hfin, ?_⟩
  simpa only [Complex.sin_arg] using sine_lower_bound_of_two_arc_bounds hθ hlreal hrreal

end SLEExactGauge.CrosscutSides

end

end OAI
