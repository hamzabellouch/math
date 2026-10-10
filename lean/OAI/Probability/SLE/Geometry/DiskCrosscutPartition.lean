import OAI.Probability.SLE.Geometry.DiskBoundaryRegion
import OAI.Probability.SLE.Geometry.TransportCrosscutPartition

namespace OAI

/-! The two bounded regions of a compact disk crosscut exhaust its complement. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

lemma diskDiameter_plane_segment :
    complexPlaneCoordinates '' (diskDiameter '' Icc 0 1)=
      segment ℝ (complexPlaneCoordinates (-1)) (complexPlaneCoordinates 1) := by
  rw [image_image,segment_eq_image_lineMap]
  congr 1
  funext s
  rw [AffineMap.lineMap_apply_module]
  change !₂[(diskDiameter s).re,(diskDiameter s).im]=
    (1-s) • !₂[(-1:ℂ).re,(-1:ℂ).im] + s • !₂[(1:ℂ).re,(1:ℂ).im]
  ext i
  fin_cases i
  · norm_num [diskDiameter]
    ring
  · norm_num [diskDiameter]

theorem disk_crosscut_partition
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    ball (0:ℂ) 1 \ (p '' Icc 0 1) =
      complexInside (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1) ∪
      complexInside (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1) ∧
    Disjoint (complexInside (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1))
      (complexInside (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1)) := by
  let c := complexPlaneCoordinates
  let C : Set ℂ := {z | ‖z‖=1}
  let P := p '' Icc 0 1
  let A := diskUpperArc '' Icc 0 1
  let B := diskLowerArc '' Icc 0 1
  obtain ⟨H,hHp,hHA⟩ := disk_crosscut_upper_straightening p hc hi h0 h1 hp
  have hHP : H '' P=diskDiameter '' Icc 0 1 := by
    ext z
    constructor
    · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
      exact ⟨s,hs,(hHp s hs).symm⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨p s,mem_image_of_mem p hs,hHp s hs⟩
  let G : Schoenflies.Plane ≃ₜ Schoenflies.Plane := (c.symm.trans H).trans c
  have hGP : G '' (c '' P)=c '' (H '' P) := by
    ext z
    simp [G]
  have hpoly : Schoenflies.IsPolygonal (G '' (c '' P)) := by
    rw [hGP,hHP,diskDiameter_plane_segment]
    exact Schoenflies.isPolygonal_segment _ _
  have hcut : Schoenflies.IsCutPair (c '' C) (c (-1)) (c 1) (c '' A) (c '' B) := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [diskUpperArc_zero,diskUpperArc_one] using
        complexPlaneCoordinates_isArcBetween diskUpperArc
          diskUpperArc_continuous.continuousOn diskUpperArc_injOn
    · simpa only [diskLowerArc_zero,diskLowerArc_one] using
        complexPlaneCoordinates_isArcBetween diskLowerArc
          diskLowerArc_continuous.continuousOn diskLowerArc_injOn
    · rw [← image_union]
      exact congrArg (fun S => c '' S) disk_semicircle_union
    · rw [← image_inter c.injective]
      rw [disk_semicircle_inter,image_pair]
  have hPin : c '' P \ {c (-1),c 1} ⊆ Schoenflies.inside (c '' C) := by
    rintro z ⟨⟨_,⟨s,hs,rfl⟩,rfl⟩,hne⟩
    have hs0 : s ≠ 0 := by
      intro he
      apply hne
      simp [he,h0]
    have hs1 : s ≠ 1 := by
      intro he
      apply hne
      simp [he,h1]
    have hball : p s ∈ ball (0:ℂ) 1 := by
      simpa only [mem_ball,dist_zero_right] using
        hp s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),lt_of_le_of_ne hs.2 hs1⟩
    have hin : p s ∈ complexInside C := by rwa [complexInside_unitDisk]
    exact hin
  have hP : Schoenflies.IsArcBetween (c '' P) (c (-1)) (c 1) := by
    simpa only [h0,h1] using complexPlaneCoordinates_isArcBetween p hc hi
  obtain ⟨he,hd⟩ := plane_crosscut_partition_of_straightening disk_circle_jordan hP hcut
    (mem_image_of_mem c (by simp)) (mem_image_of_mem c (by simp)) hPin G hpoly
  dsimp [c,C,P,A,B] at he hd
  refine ⟨?_,?_⟩
  · rw [← complexInside_unitDisk]
    apply complexPlaneCoordinates.injective.image_injective
    simpa only [image_sdiff complexPlaneCoordinates.injective,complexInside_image,image_union] using he
  · rw [Set.disjoint_left] at hd ⊢
    intro z hz hz'
    apply hd (a := complexPlaneCoordinates z)
    · have hh : complexPlaneCoordinates z ∈ Schoenflies.inside
          (complexPlaneCoordinates '' (diskUpperArc '' Icc 0 1 ∪ p '' Icc 0 1)) := hz
      simpa only [image_union] using hh
    · have hh : complexPlaneCoordinates z ∈ Schoenflies.inside
          (complexPlaneCoordinates '' (diskLowerArc '' Icc 0 1 ∪ p '' Icc 0 1)) := hz'
      simpa only [image_union] using hh

end SLEExactGauge

end

end OAI
