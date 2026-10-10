import OAI.Probability.SLE.Geometry.PublishedCrosscutStraightening
import OAI.Probability.SLE.Geometry.DiskCrosscutHomeomorph
import OAI.Probability.SLE.Geometry.HalfPlaneDiskTransport
import OAI.Probability.SLE.Geometry.ClosedHalfPlaneExtension
import OAI.Probability.SLE.Geometry.CrosscutParameterInverse

namespace OAI

/-! The relative half-plane crosscut theorem from the specified-boundary
Schönflies extension. -/
noncomputable section
open Set Complex Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem actual_halfPlaneCrosscutStraightening : PublishedHalfPlaneCrosscutStraightening := by
  intro β hc hi h0 hH hinfty
  have hβ (t : ℝ≥0) : 0 ≤ (β t).im := by
    by_cases ht : t=0
    · simp [ht,h0]
    · exact (hH t (pos_iff_ne_zero.mpr ht)).le
  obtain ⟨hpc,hpi,hpint⟩ := compactifiedCrosscut_properties β hc hi h0 hH hinfty
  obtain ⟨e,hep,hef⟩ := disk_crosscut_homeomorph (compactifiedCrosscut β) hpc hpi
    (compactifiedCrosscut_zero β h0) (compactifiedCrosscut_one β) hpint
  have he1 : e ⟨1,by norm_num⟩=⟨1,by norm_num⟩ :=
    Subtype.ext (hef ⟨1,by norm_num⟩ (by norm_num))
  obtain ⟨F,hF,hFr,hFH⟩ := closedHalfPlane_extension (halfPlaneDiskTransport e he1)
    (halfPlaneDiskTransport_boundary e he1 hef)
  refine ⟨F,hFr,hFH,?_⟩
  intro t
  rw [hF (β t) (hβ t),halfPlaneDiskTransport_apply]
  have hs := rayDiskParameter_mem t
  have hpt := compactifiedCrosscut_rayDiskParameter β t
  have hball : halfPlaneCayley (β t) ∈ closedBall (0:ℂ) 1 := by
    simpa only [mem_closedBall,dist_zero_right] using halfPlaneCayley_norm_le (hβ t)
  have hps : compactifiedCrosscut β (rayDiskParameter t) ∈ closedBall (0:ℂ) 1 :=
    hpt.symm ▸ hball
  have heq := hep (rayDiskParameter t) ⟨hs.1,hs.2.le⟩ hps
  have heq' : (e ⟨halfPlaneCayley (β t),hball⟩:ℂ)=diskDiameter (rayDiskParameter t) := by
    simpa only [hpt] using heq
  rw [heq',diskDiameter_rayDiskParameter,halfPlaneCayleyInv_cayley]
  simp

end SLEExactGauge

end

end OAI
