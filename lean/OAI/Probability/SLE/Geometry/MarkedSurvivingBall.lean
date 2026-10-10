import OAI.Probability.SLE.Geometry.MarkedCornerBounds
import OAI.Probability.SLE.Gauge.RibbonSurvival

namespace OAI

/-! The marked corner lies in a quantitative free ball of the actual
surviving component. This follows from the physical low-or-right geometry
of the completed trace, with no filled-hull containment assumption. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine

theorem marked_ball_survives
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (w : ℂ) {a : ℝ} (ha : 0 < a) (hw : 2 * a < w.im)
    (hpast : ∀ q ∈ γ '' Icc 0 T, q.im ≤ w.im - 2 * a ∨ w.re + 2 * a ≤ q.re) :
    ball w a ⊆ survivingDomain γ T := by
  intro z hz
  have hd : ‖z - w‖ < a := by simpa only [mem_ball, dist_eq_norm] using hz
  have hr := (Complex.abs_re_le_norm (z - w)).trans_lt hd
  have hi := (Complex.abs_im_le_norm (z - w)).trans_lt hd
  rw [Complex.sub_re] at hr
  rw [Complex.sub_im] at hi
  have hfree : range (upwardRay z) ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    rintro q ⟨u, rfl⟩
    have hre : (upwardRay z u).re = z.re := by simp [upwardRay]
    have him : (upwardRay z u).im = z.im + (u : ℝ) := by simp [upwardRay]
    refine ⟨?_, ?_⟩
    · change 0 < (upwardRay z u).im
      rw [him]
      linarith [(abs_lt.mp hi).1, u.coe_nonneg]
    · intro hq
      rcases hpast _ hq with hq | hq
      · rw [him] at hq
        linarith [(abs_lt.mp hi).1, u.coe_nonneg]
      · rw [hre] at hq
        linarith [(abs_lt.mp hr).2]
  have hs := survives_of_unbounded_free_curve γ T (upwardRay z)
    (upwardRay_continuous z) hfree (upwardRay_unbounded z) (mem_range_self 0)
  simpa only [upwardRay, NNReal.coe_zero, Complex.ofReal_zero, zero_mul, add_zero] using hs

lemma marked_corner_ball_survives
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (w : ℂ) {a : ℝ} (ha : 0 < a) (hw : 2 * a < w.im)
    (hpast : ∀ q ∈ γ '' Icc 0 T, q.im ≤ w.im - 2 * a ∨ w.re + 2 * a ≤ q.re) :
    MapsTo (markedCornerChart w) (ball (0 : ℂ) (a / 12)) (survivingDomain γ T) := by
  intro z hz
  apply marked_ball_survives γ T w ha hw hpast
  have hn : ‖z‖ < a / 12 := by simpa only [mem_ball, dist_zero_right] using hz
  exact (markedCornerChart_norm w z).trans_lt (by linarith)

end SLEExactGauge.Serpentine

end

end OAI
