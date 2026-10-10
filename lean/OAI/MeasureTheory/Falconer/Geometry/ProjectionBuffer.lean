import OAI.MeasureTheory.Falconer.Geometry.ProjectionGood

namespace OAI

/-! # Directional buffers for the actual full-law projection test -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionCollision_direction_transfer (μ : Measure (Space d))
    {D δ W W' : ℝ} (hD : 0 ≤ D) (_hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Space d} (hvw : ‖v-w‖ ≤ δ) (hwidth : W+D*δ ≤ W') :
    projectionCollision μ v W ≤ projectionCollision μ w W' := by
  apply measure_mono_ae
  filter_upwards [hsupport] with z hz
  intro htest
  have hinner : |inner ℝ (z.1-z.2) (w-v)| ≤ D*δ := by
    have hnorm : ‖w-v‖ ≤ δ := by simpa only [norm_sub_rev] using hvw
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hz hnorm (norm_nonneg _) hD)
  have he : inner ℝ (z.1-z.2) w = inner ℝ (z.1-z.2) v+inner ℝ (z.1-z.2) (w-v) := by
    rw [inner_sub_right]
    ring
  change |inner ℝ (z.1-z.2) v| ≤ W at htest
  change |inner ℝ (z.1-z.2) w| ≤ W'
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add htest hinner).trans hwidth)

theorem projectionGoodSet_buffer (μ : Measure (Space d))
    {D δ W W' T : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Sphere d} (hvw : dist v w ≤ δ) (hwidth : W+D*δ ≤ W')
    (hw : w ∈ projectionGoodSet μ W' T) : v ∈ projectionGoodSet μ W T := by
  have hd : ‖(v:Space d)-(w:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hvw
  exact (projectionCollision_direction_transfer μ hD hδ hsupport hd hwidth).trans hw

end Falconer

end OAI
