import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryParam
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

/-! The actual coordinate disks are regular open, with exactly the stated
coordinate circles as their frontiers. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

private lemma complex_radius_sq (c x : Base) :
    ‖Complex.equivRealProdCLM.symm x - Complex.equivRealProdCLM.symm c‖^2 =
      circularRadiusSquared c x := by
  rw [← map_sub,Complex.sq_norm]
  simp [Complex.equivRealProdCLM_symm_apply,Complex.normSq_apply,circularRadiusSquared,pow_two]

private lemma circular_region_ball (c : Base) {r : ℝ} (hr : 0 < r) :
    {x | circularRadiusSquared c x < r^2} =
      Complex.equivRealProdCLM.symm ⁻¹' ball (Complex.equivRealProdCLM.symm c) r := by
  ext x
  rw [mem_preimage,mem_ball,dist_eq_norm]
  change circularRadiusSquared c x < r^2 ↔ _
  rw [← complex_radius_sq]
  exact sq_lt_sq₀ (norm_nonneg _) hr.le

private lemma circular_region_closedBall (c : Base) {r : ℝ} (hr : 0 < r) :
    {x | circularRadiusSquared c x ≤ r^2} =
      Complex.equivRealProdCLM.symm ⁻¹' closedBall (Complex.equivRealProdCLM.symm c) r := by
  ext x
  rw [mem_preimage,mem_closedBall,dist_eq_norm]
  change circularRadiusSquared c x ≤ r^2 ↔ _
  rw [← complex_radius_sq]
  exact sq_le_sq₀ (norm_nonneg _) hr.le

lemma closure_circular_region (c : Base) {r : ℝ} (hr : 0 < r) :
    closure {x | circularRadiusSquared c x < r^2} = {x | circularRadiusSquared c x ≤ r^2} := by
  rw [circular_region_ball c hr]
  change closure (Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' ball
    (Complex.equivRealProdCLM.symm c) r) = _
  rw [← Complex.equivRealProdCLM.symm.toHomeomorph.preimage_closure,closure_ball _ hr.ne']
  exact (circular_region_closedBall c hr).symm

lemma interior_circular_region (c : Base) {r : ℝ} (hr : 0 < r) :
    interior {x | circularRadiusSquared c x ≤ r^2} = {x | circularRadiusSquared c x < r^2} := by
  rw [circular_region_closedBall c hr]
  change interior (Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' closedBall
    (Complex.equivRealProdCLM.symm c) r) = _
  rw [← Complex.equivRealProdCLM.symm.toHomeomorph.preimage_interior,interior_closedBall _ hr.ne']
  exact (circular_region_ball c hr).symm

end ClosedSurfaceR4.PhaseGeometry
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_iff (q : M) {r : ℝ}
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) (p : M) :
    p ∈ circularDiskClosure q r ↔ p ∈ (coordinateChart q).source ∧
      circularRadiusSquared (coordinateChart q q) (coordinateChart q p) ≤ r^2 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(coordinateChart q).map_target (hreg hx),?_⟩
    rwa [(coordinateChart q).right_inv (hreg hx)]
  · rintro ⟨hp,hx⟩
    exact ⟨coordinateChart q p,hx,(coordinateChart q).left_inv hp⟩

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_closure (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    closure (circularCoordinateDisk q r) = circularDiskClosure q r := by
  let S := {x : SmallModes.Base | circularRadiusSquared (coordinateChart q q) x < r^2}
  have hI : (coordinateChart q).IsImage (circularCoordinateDisk q r) S := by
    intro p hp
    exact ⟨fun hx => ⟨hp,hx⟩,fun hx => hx.2⟩
  have hc : closure (circularCoordinateDisk q r) ⊆ circularDiskClosure q r := by
    apply closure_minimal _ (circularDiskClosure_compact q r hreg).isClosed
    intro p hp
    exact (circularDiskClosure_iff q hreg p).mpr ⟨hp.1,hp.2.le⟩
  apply Subset.antisymm hc
  intro p hp
  obtain ⟨hs,hx⟩ := (circularDiskClosure_iff q hreg p).mp hp
  apply (hI.closure hs).mp
  simpa only [S,closure_circular_region _ hr,mem_ofPred] using hx

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_interior (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    interior (circularDiskClosure q r) = circularCoordinateDisk q r := by
  let S := {x : SmallModes.Base | circularRadiusSquared (coordinateChart q q) x ≤ r^2}
  have hI : (coordinateChart q).IsImage (circularDiskClosure q r) S := by
    intro p hp
    exact ⟨fun hx => (circularDiskClosure_iff q hreg p).mpr ⟨hp,hx⟩,
      fun hx => ((circularDiskClosure_iff q hreg p).mp hx).2⟩
  ext p
  constructor
  · intro hp
    have hs := circularDiskClosure_source q r hreg (interior_subset hp)
    have hx := (hI.interior hs).mpr hp
    exact ⟨hs,by simpa only [S,interior_circular_region _ hr,mem_ofPred,mem_preimage] using hx⟩
  · intro hp
    apply (circularCoordinateDisk_open q r).subset_interior_iff.mpr ?_ hp
    exact fun p hp => (circularDiskClosure_iff q hreg p).mpr ⟨hp.1,hp.2.le⟩

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_frontier (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    frontier (circularCoordinateDisk q r) = circularBoundary q r := by
  rw [frontier,circularCoordinateDisk_closure q hr hreg,
    (circularCoordinateDisk_open q r).interior_eq]
  ext p
  simp only [Set.mem_sdiff,circularDiskClosure_iff q hreg p,circularCoordinateDisk,circularBoundary,
    mem_inter_iff,mem_preimage,mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hp,hle⟩,hn⟩
    exact ⟨hp,le_antisymm hle (not_lt.mp (fun hlt => hn ⟨hp,hlt⟩))⟩
  · rintro ⟨hp,he⟩
    exact ⟨⟨hp,he.le⟩,fun hlt => (lt_irrefl _ (he ▸ hlt.2))⟩

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_regular (q : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) :
    interior (closure (circularCoordinateDisk q r)) = circularCoordinateDisk q r := by
  rw [circularCoordinateDisk_closure q hr hreg,circularDiskClosure_interior q hr hreg]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
