import OAI.Geometry.IsometricImmersion.Coordinates.RoundDisk
import OAI.Geometry.IsometricImmersion.Immersions.CompactBoundaryExtremum
import OAI.Geometry.IsometricImmersion.Immersions.RankOne2

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
variable {center : Coord} {radius : ℝ}

theorem exists_roundDisk_boundary_nonzero_secondFundamental
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hr : 0 < radius) (hDU : roundClosedDisk center radius ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk center radius, gaussianCurvature g p < 0) :
    ∃ b ∈ frontier (roundClosedDisk center radius),
      secondFundamental F (unitNormalField F b) b ≠ 0 := by
  by_contra hnone
  have hcircle : ∀ t, coordinateCircle center radius t ∈ U :=
    fun t => hDU (coordinateCircle_mem_roundClosedDisk center radius t)
  have hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0 := by
    intro t
    by_contra ht
    exact hnone ⟨coordinateCircle center radius t,
      coordinateCircle_mem_frontier_roundClosedDisk center hr t, ht⟩
  obtain ⟨e, c, he, _, _, hh⟩ :=
    exists_circle_constant_normal_and_height hg hF hU hcircle hII
  have hK' : ∀ p ∈ interior (roundClosedDisk center radius), gaussianCurvature g p < 0 := by
    intro p hp
    exact hK p (by simpa only [interior_roundClosedDisk center hr] using hp)
  apply immersion_height_not_constant_frontier hg hF hU
    (isCompact_roundClosedDisk center hr) hDU
    (interior_roundClosedDisk_nonempty center hr) hK' e he
  refine ⟨c, ?_⟩
  intro p hp
  obtain ⟨t, rfl⟩ := exists_coordinateCircle_of_mem_frontier_roundClosedDisk center p hr hp
  exact hh t

theorem roundDisk_boundary_rank_one
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hr : 0 < radius) (hDU : roundClosedDisk center radius ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk center radius, gaussianCurvature g p < 0)
    (hKboundary : ∀ p ∈ frontier (roundClosedDisk center radius), gaussianCurvature g p = 0) :
    ∃ b ∈ frontier (roundClosedDisk center radius),
      secondFundamental F (unitNormalField F b) b ≠ 0 ∧
      (secondFundamental F (unitNormalField F b) b).rank = 1 := by
  obtain ⟨b, hb, hII⟩ := exists_roundDisk_boundary_nonzero_secondFundamental
    hg hF hU hr hDU hK
  have hbD : b ∈ roundClosedDisk center radius :=
    ((mem_frontier_roundClosedDisk_iff center b hr).mp hb).le
  have hbU : b ∈ U := hDU hbD
  have hdet := det_secondFundamental_eq_gaussianCurvature_mul_det hg hF hU hbU
    (unitNormalField_isUnitNormalAt hg hF hbU)
  rw [hKboundary b hb, zero_mul] at hdet
  exact ⟨b, hb, hII, two_by_two_rank_eq_one_of_ne_zero_det_eq_zero hII hdet⟩

theorem exists_roundDisk_boundary_unitNormal_rank_one
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hr : 0 < radius) (hDU : roundClosedDisk center radius ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk center radius, gaussianCurvature g p < 0)
    (hKboundary : ∀ p ∈ frontier (roundClosedDisk center radius), gaussianCurvature g p = 0) :
    ∃ b ∈ frontier (roundClosedDisk center radius), ∃ n : Ambient,
      IsUnitNormalAt F n b ∧ secondFundamental F n b ≠ 0 ∧
      (secondFundamental F n b).rank = 1 := by
  obtain ⟨b, hb, hII, hrank⟩ := roundDisk_boundary_rank_one hg hF hU hr hDU hK hKboundary
  have hbU : b ∈ U := hDU (((mem_frontier_roundClosedDisk_iff center b hr).mp hb).le)
  exact ⟨b, hb, unitNormalField F b, unitNormalField_isUnitNormalAt hg hF hbU, hII, hrank⟩

end SmoothLocal.Geometry

end

end OAI
