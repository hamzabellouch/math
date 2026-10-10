import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests

namespace OAI

/-!
# Transferring cell oscillation bounds

Localization independence transfers scalar Riesz oscillation bounds to a contained
ball. Comparing the centers and scales then turns a cell-centered bound into the
corresponding normalized bound on a nearby ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem ScalarOscillationBound.of_ball_subset {p d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (a b : Ambient d) (r R v w : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hsub : ball a r ⊆ ball b R) (hvw : v ≤ w)
    (hosc : ScalarOscillationBound (p + 1) μ b R v) :
    ScalarOscillationBound (p + 1) μ a r w := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  intro e he φ hφ hs hzero
  have hsA : ∀ x, φ x ≠ 0 → dist x a ≤ r := fun x hx =>
    (hs (subset_tsupport _ hx)).le
  have hsB : ∀ x, φ x ≠ 0 → dist x b ≤ R := fun x hx =>
    (hsub (hs (subset_tsupport _ hx))).le
  have heq := rieszScalarPairing_localization_independent p G μ hg e φ 1 hφ
    a b r R (2 * r) (2 * R) hr.le hR.le (by positivity) (by positivity)
    le_rfl le_rfl hsA hsB hzero
  rw [heq]
  exact (hosc e he φ hφ (hs.trans hsub) hzero).trans hvw

theorem cell_oscillation_controls_nearby_ball {p d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (a z : Ambient d) (s r H T δ : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hH : 0 < H) (hT : 0 < T) (hδ : 0 ≤ δ)
    (hnear : dist a z ≤ 2 * r) (hupper : s ≤ H * r) (hlower : (H / 64) * r ≤ s)
    (hosc : ScalarOscillationBound (p + 1) μ z ((H * T + 2) * r)
      (((H / 64) ^ (p + 2) * δ ^ 3) * r ^ (p + 2))) :
    ScalarOscillationBound (p + 1) μ a (s * T) (s ^ (p + 2) * δ ^ 3) := by
  apply ScalarOscillationBound.of_ball_subset μ G hg a z (s * T) ((H * T + 2) * r)
    _ _ (mul_pos hs hT) (by positivity) _ _ hosc
  · apply ball_subset_outer_of_radius_dist
    nlinarith [mul_le_mul_of_nonneg_right hupper hT.le]
  · have hp := pow_le_pow_left₀ (show 0 ≤ (H / 64) * r by positivity) hlower (p + 2)
    have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hδ 3)
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using! hm

end

end RieszRectifiability

end OAI
