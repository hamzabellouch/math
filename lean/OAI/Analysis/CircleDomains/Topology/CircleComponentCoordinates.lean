import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks

namespace OAI

/-!
# Center and radius coordinates of circle-domain components

If a circle domain contains infinity, every complementary component
is an ordinary closed disk, allowing radius zero. A bound on the whole
complement bounds both parameters. Thus no choice of disk coordinates
is an extra hypothesis in the marked-disk compactness argument.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem circleDomain_component_eq_closedBall
    {V : Set Sphere} (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {p : Sphere} (hp : p ∈ Vᶜ) :
    ∃ (c : ℂ) (r : ℝ), 0 ≤ r ∧
      connectedComponentIn Vᶜ p = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  have hnot : OnePoint.infty ∉ connectedComponentIn Vᶜ p := by
    intro h
    exact connectedComponentIn_subset Vᶜ p h hinf
  rcases hV.2.2 p hp with ⟨q, hq⟩ | hq
  · have hqfinite : q ≠ OnePoint.infty := by
      intro h
      apply hnot
      rw [hq, ← h]
      exact mem_singleton q
    refine ⟨finiteCoord q, 0, le_rfl, ?_⟩
    rw [Metric.closedBall_zero, image_singleton, coe_finiteCoord hqfinite]
    exact hq
  · obtain ⟨c, r, hr, he⟩ := isRoundClosedDisk_eq_euclidean hq hnot
    exact ⟨c, r, hr.le, he⟩

theorem closedBall_parameters_bound
    {c : ℂ} {r L : ℝ} (hr : 0 ≤ r)
    (hsub : Metric.closedBall c r ⊆ Metric.closedBall (0 : ℂ) L) :
    ‖c‖ ≤ L ∧ r ≤ L := by
  have hcenter : ‖c‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hsub (Metric.mem_closedBall_self hr)
  have hplus : c + (r : ℂ) ∈ Metric.closedBall c r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, le_refl]
  have hminus : c - (r : ℂ) ∈ Metric.closedBall c r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, le_refl]
  have hp : ‖c + (r : ℂ)‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hplus
  have hm : ‖c - (r : ℂ)‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hminus
  have hdiam := norm_sub_le (c + (r : ℂ)) (c - (r : ℂ))
  have heq : c + (r : ℂ) - (c - (r : ℂ)) = (2 * r : ℝ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hdiam
  exact ⟨hcenter, by linarith⟩

theorem bounded_circleDomain_component_parameters
    {V : Set Sphere} (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 L)
    {p : Sphere} (hp : p ∈ Vᶜ) :
    ∃ (c : ℂ) (r : ℝ), ‖c‖ ≤ L ∧ r ∈ Icc 0 L ∧
      connectedComponentIn Vᶜ p = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  obtain ⟨c, r, hr, he⟩ := circleDomain_component_eq_closedBall hV hinf hp
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall (0 : ℂ) L := by
    intro z hz
    have hzs : (z : Sphere) ∈ connectedComponentIn Vᶜ p := by
      rw [he]
      exact mem_image_of_mem _ hz
    have hb := hbound (connectedComponentIn_subset Vᶜ p hzs)
    exact OnePoint.coe_injective.mem_set_image.mp hb
  obtain ⟨hc, hrL⟩ := closedBall_parameters_bound hr hsub
  exact ⟨c, r, hc, ⟨hr, hrL⟩, he⟩

end CircleDomainRigidity

end

end OAI
