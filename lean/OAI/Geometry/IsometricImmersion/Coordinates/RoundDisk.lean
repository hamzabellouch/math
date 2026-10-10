import OAI.Geometry.IsometricImmersion.Immersions.BoundaryNormal
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Metric

namespace SmoothLocal.Geometry

def roundRadiusSq (center p : Coord) : ℝ :=
  (p 0 - center 0) ^ 2 + (p 1 - center 1) ^ 2

def roundClosedDisk (center : Coord) (radius : ℝ) : Set Coord :=
  {p | roundRadiusSq center p ≤ radius ^ 2}

def roundOpenDisk (center : Coord) (radius : ℝ) : Set Coord :=
  {p | roundRadiusSq center p < radius ^ 2}

def euclideanPlaneCoordinates : Coord ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

theorem euclideanPlaneCoordinates_dist_sq (p center : Coord) :
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) ^ 2 =
      roundRadiusSq center p := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

theorem roundClosedDisk_eq_preimage_closedBall (center : Coord) {radius : ℝ}
    (hr : 0 ≤ radius) :
    roundClosedDisk center radius = euclideanPlaneCoordinates ⁻¹'
      closedBall (euclideanPlaneCoordinates center) radius := by
  ext p
  change roundRadiusSq center p ≤ radius ^ 2 ↔
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) ≤ radius
  rw [← euclideanPlaneCoordinates_dist_sq]
  exact sq_le_sq₀ dist_nonneg hr

theorem roundOpenDisk_eq_preimage_ball (center : Coord) {radius : ℝ}
    (hr : 0 ≤ radius) :
    roundOpenDisk center radius = euclideanPlaneCoordinates ⁻¹'
      ball (euclideanPlaneCoordinates center) radius := by
  ext p
  change roundRadiusSq center p < radius ^ 2 ↔
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) < radius
  rw [← euclideanPlaneCoordinates_dist_sq]
  exact sq_lt_sq₀ dist_nonneg hr

theorem isCompact_roundClosedDisk (center : Coord) {radius : ℝ} (hr : 0 < radius) :
    IsCompact (roundClosedDisk center radius) := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  exact euclideanPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (euclideanPlaneCoordinates center) radius)

theorem interior_roundClosedDisk (center : Coord) {radius : ℝ} (hr : 0 < radius) :
    interior (roundClosedDisk center radius) = roundOpenDisk center radius := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  change interior (euclideanPlaneCoordinates.toHomeomorph ⁻¹'
    closedBall (euclideanPlaneCoordinates center) radius) = _
  rw [← euclideanPlaneCoordinates.toHomeomorph.preimage_interior,
    interior_closedBall _ hr.ne']
  exact (roundOpenDisk_eq_preimage_ball center hr.le).symm

theorem center_mem_interior_roundClosedDisk (center : Coord) {radius : ℝ}
    (hr : 0 < radius) : center ∈ interior (roundClosedDisk center radius) := by
  rw [interior_roundClosedDisk center hr]
  simpa [roundOpenDisk, roundRadiusSq] using sq_pos_of_pos hr

theorem interior_roundClosedDisk_nonempty (center : Coord) {radius : ℝ}
    (hr : 0 < radius) : (interior (roundClosedDisk center radius)).Nonempty :=
  ⟨center, center_mem_interior_roundClosedDisk center hr⟩

theorem mem_frontier_roundClosedDisk_iff (center p : Coord) {radius : ℝ}
    (hr : 0 < radius) :
    p ∈ frontier (roundClosedDisk center radius) ↔ roundRadiusSq center p = radius ^ 2 := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  change p ∈ frontier (euclideanPlaneCoordinates.toHomeomorph ⁻¹'
    closedBall (euclideanPlaneCoordinates center) radius) ↔ _
  rw [← euclideanPlaneCoordinates.toHomeomorph.preimage_frontier,
    frontier_closedBall _ hr.ne']
  change dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) = radius ↔ _
  rw [← sq_eq_sq₀ dist_nonneg hr.le, euclideanPlaneCoordinates_dist_sq]

theorem coordinateCircle_mem_roundClosedDisk (center : Coord) (radius t : ℝ) :
    coordinateCircle center radius t ∈ roundClosedDisk center radius := by
  change roundRadiusSq center (coordinateCircle center radius t) ≤ radius ^ 2
  exact (coordinateCircle_equation center radius t).le

theorem coordinateCircle_mem_frontier_roundClosedDisk (center : Coord) {radius : ℝ}
    (hr : 0 < radius) (t : ℝ) :
    coordinateCircle center radius t ∈ frontier (roundClosedDisk center radius) := by
  rw [mem_frontier_roundClosedDisk_iff center _ hr]
  exact coordinateCircle_equation center radius t

theorem exists_coordinateCircle_of_roundRadiusSq_eq (center p : Coord) {radius : ℝ}
    (hr : 0 < radius) (hp : roundRadiusSq center p = radius ^ 2) :
    ∃ t : ℝ, coordinateCircle center radius t = p := by
  let z : ℂ := ⟨p 0 - center 0, p 1 - center 1⟩
  have hnorm : ‖z‖ = radius := by
    apply (sq_eq_sq₀ (norm_nonneg z) hr.le).mp
    rw [Complex.sq_norm]
    simpa only [Complex.normSq_apply, z, roundRadiusSq, pow_two] using hp
  have hcos : radius * Real.cos z.arg = p 0 - center 0 := by
    simpa only [hnorm, z] using Complex.norm_mul_cos_arg z
  have hsin : radius * Real.sin z.arg = p 1 - center 1 := by
    simpa only [hnorm, z] using Complex.norm_mul_sin_arg z
  refine ⟨z.arg, ?_⟩
  funext i
  fin_cases i
  · change center 0 + radius * Real.cos z.arg = p 0
    linarith
  · change center 1 + radius * Real.sin z.arg = p 1
    linarith

theorem exists_coordinateCircle_of_mem_frontier_roundClosedDisk (center p : Coord)
    {radius : ℝ} (hr : 0 < radius) (hp : p ∈ frontier (roundClosedDisk center radius)) :
    ∃ t : ℝ, coordinateCircle center radius t = p :=
  exists_coordinateCircle_of_roundRadiusSq_eq center p hr
    ((mem_frontier_roundClosedDisk_iff center p hr).mp hp)

theorem frontier_roundClosedDisk_eq_range (center : Coord) {radius : ℝ} (hr : 0 < radius) :
    frontier (roundClosedDisk center radius) = Set.range (coordinateCircle center radius) := by
  ext p
  constructor
  · intro hp
    exact exists_coordinateCircle_of_mem_frontier_roundClosedDisk center p hr hp
  · rintro ⟨t, rfl⟩
    exact coordinateCircle_mem_frontier_roundClosedDisk center hr t

end SmoothLocal.Geometry

end

end OAI
