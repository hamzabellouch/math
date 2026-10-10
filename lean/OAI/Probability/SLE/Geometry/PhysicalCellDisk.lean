import OAI.Probability.SLE.Geometry.DiskQuarterGeometry
import OAI.Probability.SLE.Multipoint.MultipointPhysicalGeometry

namespace OAI

/-! Physical quarter-disk charts at actual surviving Loewner points. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.quarter_disk_chart_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hR : 0 < fullRadius G t z) :
    let f := physicalDiskChart id F G t z
    IsCompact (f '' closedBall 0 (1/4)) ∧
    closedBall z (fullRadius G t z / (1024 * Real.pi)) ⊆ f '' closedBall 0 (1/4) ∧
    f '' closedBall 0 (1/4) ⊆ closedBall z (2*fullRadius G t z) ∧
    f '' closedBall 0 (1/4) ⊆ survivingDomain γ t ∧
    ∀ w ∈ closedBall (0:ℂ) (1/4), ‖deriv f w‖ ≤ 16*fullRadius G t z := by
  let f := physicalDiskChart id F G t z
  obtain ⟨hd,hi,hzero,hder,_⟩ := hw.physical_disk_chart id differentiableOn_id
    (fun _ _ _ _ h => h) t z hz
  change DifferentiableOn ℂ f (ball 0 1) at hd
  change InjOn f (ball 0 1) at hi
  change f 0=z at hzero
  have hder' : ‖deriv f 0‖ = fullRadius G t z := by
    change ‖deriv f 0‖ = physicalConformalRadius id G t z at hder
    simpa [physicalConformalRadius] using hder
  have hsub : closedBall (0:ℂ) (1/4) ⊆ ball 0 1 := by
    intro w hw
    have hh : ‖w‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_zero_right] using hw
    apply mem_ball_zero_iff.mpr
    linarith
  refine ⟨(isCompact_closedBall _ _).image_of_continuousOn (hd.continuousOn.mono hsub),?_,?_,?_,?_⟩
  · simpa only [hzero,hder'] using univalent_quarter_closed_image_contains hd hi (hder' ▸ hR)
  · simpa only [hzero,hder'] using univalent_quarter_closed_image_bound hgrowth hd hi
  · rintro _ ⟨w,hw',rfl⟩
    have hgw : 0 < (G t z).im := hw.imag_positive t z hz
    have hmap := diskToHalfPlane_maps hgw (hsub hw')
    rcases hw with ⟨_,_,_,_,_,_,hFmap,_,_,_,_,_,_⟩
    exact hFmap t hmap
  · intro w hw'
    have hn : ‖w‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_zero_right] using hw'
    simpa only [hder'] using univalent_quarter_derivative_upper hgrowth hd hi hn

end SLEExactGauge

end

end OAI
