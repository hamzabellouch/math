import OAI.Analysis.CircleDomains.Topology.DiskCentering

namespace OAI

/-! The centering formula is an actual homeomorphism of the closed disk. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def diskCenteringHomeomorph (a : ℂ) (ha : ‖a‖ < 1) :
    closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 where
  toFun z := ⟨diskCentering a z.val, by
    simpa only [mem_closedBall_zero_iff] using
      diskCentering_norm_le ha (mem_closedBall_zero_iff.mp z.property)⟩
  invFun z := ⟨diskCentering (-a) z.val, by
    simpa only [mem_closedBall_zero_iff] using
      diskCentering_norm_le (by simpa only [norm_neg] using ha)
        (mem_closedBall_zero_iff.mp z.property)⟩
  left_inv z := Subtype.ext (diskCentering_inverse ha (mem_closedBall_zero_iff.mp z.property))
  right_inv z := Subtype.ext (by
    simpa only [neg_neg] using diskCentering_inverse
      (a := -a) (by simpa only [norm_neg] using ha) (mem_closedBall_zero_iff.mp z.property))
  continuous_toFun := ((continuousOn_diskCentering ha).comp_continuous continuous_subtype_val
    (fun z => z.property)).subtype_mk _
  continuous_invFun := ((continuousOn_diskCentering (by simpa only [norm_neg] using ha)).comp_continuous
    continuous_subtype_val (fun z => z.property)).subtype_mk _

theorem diskCentering_injOn (a : ℂ) (ha : ‖a‖ < 1) :
    InjOn (diskCentering a) (closedBall (0 : ℂ) 1) := by
  intro z hz w hw h
  have he := congrArg (diskCentering (-a)) h
  rwa [diskCentering_inverse ha (mem_closedBall_zero_iff.mp hz),
    diskCentering_inverse ha (mem_closedBall_zero_iff.mp hw)] at he

end CircleDomainRigidity

end

end OAI
