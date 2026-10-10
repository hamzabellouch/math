import OAI.MathematicalPhysics.Transonic.Shooting.FiniteProfile
import OAI.MathematicalPhysics.Transonic.Shooting.MatchedExistence

namespace OAI

namespace SepticProfile.SonicShooting
open Set SourceFamily AxisBarriers
open scoped ContDiff

/-- A selected-parameter finite transonic source profile. -/
theorem exists_finite_transonic : ∃ (p : Parameter) (w : ℝ) (u : ℝ → ℝ),
    0<w ∧ ContDiffOn ℝ ∞ u (Icc 0 (1+w)) ∧
    (∀ z ∈ Icc (0:ℝ) (1+w), D (sig p) z (u z)*deriv u z=N (kap p) z (u z)) ∧
    (∀ z ∈ Ioo (0:ℝ) 1, u z ∈ Ioo (0:ℝ) 1) ∧
    (∀ z ∈ Ioc (0:ℝ) (1+w), u z=1 ↔ z=1) ∧ 0<deriv u 1 := by
  obtain ⟨M⟩ := exists_matched_pair
  exact ⟨M.parameter,M.sonic.width,M.localProfile,M.sonic.width_pos,
    fun z hz => (M.local_smooth_at hz).contDiffWithinAt,fun _ hz => M.local_equation hz,
    fun _ hz => M.local_range hz,fun _ hz => M.local_unique_sonic hz,M.local_slope⟩

end SepticProfile.SonicShooting

end OAI
