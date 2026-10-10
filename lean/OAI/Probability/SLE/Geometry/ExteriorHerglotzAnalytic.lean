import OAI.Probability.SLE.Geometry.ExteriorHerglotzTransform

namespace OAI

/-! The hydrodynamic singularity of the inverted transform is removable.
Only analyticity outside the chosen circle is required. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma exteriorHerglotzTransform_eq_raw {G : ℂ → ℂ} {R c : ℝ} {w : ℂ}
    (hw : w≠0) : exteriorHerglotzTransform G R c w=exteriorHerglotzRaw G R w :=
  Function.update_of_ne hw _ _

lemma exteriorHerglotzTransform_differentiableAt_ne_zero {G : ℂ → ℂ} {R c : ℝ}
    (hR : 0<R) (hG : ∀ z : ℂ, R≤‖z‖ → DifferentiableAt ℂ G z)
    {w : ℂ} (hw : w≠0) (hw1 : ‖w‖≤1) :
    DifferentiableAt ℂ (exteriorHerglotzTransform G R c) w := by
  have hn : 0<‖w‖ := norm_pos_iff.mpr hw
  have hz : R≤‖(R:ℂ)/w‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    exact (le_div_iff₀ hn).mpr (mul_le_of_le_one_right hR.le hw1)
  have hi : DifferentiableAt ℂ (fun v : ℂ => (R:ℂ)/v) w :=
    (differentiableAt_const (R:ℂ)).div differentiableAt_id hw
  have hd : DifferentiableAt ℂ (exteriorHerglotzRaw G R) w :=
    ((((differentiableAt_const (1:ℂ)).sub (differentiableAt_id.pow 2)).div
      differentiableAt_id hw).mul (((hG _ hz).comp w hi).sub hi))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hw] with v hv
  exact exteriorHerglotzTransform_eq_raw hv

theorem exteriorHerglotzTransform_differentiableOn {G : ℂ → ℂ} {R c : ℝ}
    (hR : 0<R) (hG : ∀ z : ℂ, R≤‖z‖ → DifferentiableAt ℂ G z)
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ))) :
    DifferentiableOn ℂ (exteriorHerglotzTransform G R c) (closedBall 0 1) := by
  have hzero : DifferentiableAt ℂ (exteriorHerglotzTransform G R c) 0 := by
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
      (exteriorHerglotzTransform_continuousAt_zero hR.ne' hc)).differentiableAt
    have hb : ∀ᶠ w : ℂ in 𝓝[≠] (0:ℂ), w∈ball 0 1 :=
      Filter.Eventually.filter_mono inf_le_left (ball_mem_nhds (0:ℂ) zero_lt_one)
    filter_upwards [self_mem_nhdsWithin,hb] with w hw hw1
    exact exteriorHerglotzTransform_differentiableAt_ne_zero hR hG hw
      (mem_ball_zero_iff.mp hw1).le
  intro w hw
  rcases eq_or_ne w 0 with rfl|hne
  · exact hzero.differentiableWithinAt
  · exact (exteriorHerglotzTransform_differentiableAt_ne_zero hR hG hne
      (mem_closedBall_zero_iff.mp hw)).differentiableWithinAt

end SLEExactGauge

end

end OAI
