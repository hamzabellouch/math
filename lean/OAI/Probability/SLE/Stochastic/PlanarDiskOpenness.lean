import OAI.Probability.SLE.Stochastic.PlanarDiskImage

namespace OAI

/-! The planar open-disk specialization of invariance of domain, proved
from compact boundary separation and the exponential-covering argument. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

theorem actual_planarDiskOpenness : PublishedPlanarDiskOpenness := by
  intro f x r _hr hf hi
  apply Metric.isOpen_iff.mpr
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨R,hR,hRa⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_ball.mem_nhds ha)
  let F : ℂ → ℂ := fun z => f (a+z)
  have htrans (z : ℂ) (hz : z∈closedBall 0 R) : a+z∈ball x r := by
    apply hRa
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  have hFc : ContinuousOn F (closedBall 0 R) :=
    hf.comp (continuous_const.add continuous_id).continuousOn htrans
  have hFi : InjOn F (closedBall 0 R) := by
    intro z hz w hw he
    exact add_left_cancel (hi (htrans z hz) (htrans w hw) he)
  have hpos (z : ℂ) (hz : z∈sphere (0:ℂ) R) : 0<‖F z-F 0‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hez : z=0 := hFi (sphere_subset_closedBall hz) (mem_closedBall_self hR.le)
      (sub_eq_zero.mp he)
    have hzr : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    rw [hez,norm_zero] at hzr
    exact hR.ne' hzr.symm
  obtain ⟨δ,hδ,hsep⟩ := (isCompact_sphere (0:ℂ) R).exists_forall_le'
    ((hFc.mono sphere_subset_closedBall).sub continuousOn_const).norm hpos
  refine ⟨δ,hδ,fun y hy => ?_⟩
  have hfy : y∈ball (F 0) δ := by simpa only [F,add_zero] using hy
  obtain ⟨z,hz,hFz⟩ := planar_closedBall_image_contains_ball F R δ hR hFc hFi hsep hfy
  exact ⟨a+z,htrans z hz,hFz⟩

end SLEExactGauge

end

end OAI
