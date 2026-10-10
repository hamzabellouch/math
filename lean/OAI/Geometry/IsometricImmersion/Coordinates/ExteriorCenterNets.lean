import OAI.Geometry.IsometricImmersion.Coordinates.ExteriorAnnuli

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem accumulatingDisk_frontier_isCompact (n : ℕ) :
    IsCompact (frontier (accumulatingDisk n)) := by
  apply (accumulatingDisk_isCompact n).of_isClosed_subset isClosed_frontier
  simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using
    (frontier_subset_closure : frontier (accumulatingDisk n) ⊆ closure (accumulatingDisk n))

theorem exists_finite_disk_boundary_net (n k : ℕ) :
    ∃ s : Finset Coord, (∀ p ∈ s, p ∈ frontier (accumulatingDisk n)) ∧
      ∀ p ∈ frontier (accumulatingDisk n), ∃ q ∈ s, dist p q < accumulatingScale k := by
  classical
  obtain ⟨s, hsfront, hsfin, hcover⟩ :=
    (accumulatingDisk_frontier_isCompact n).finite_cover_balls (accumulatingScale_pos k)
  refine ⟨hsfin.toFinset, ?_, ?_⟩
  · intro p hp
    exact hsfront (hsfin.mem_toFinset.mp hp)
  · intro p hp
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hcover hp)
    obtain ⟨hqs, hpq⟩ := Set.mem_iUnion.mp hq
    exact ⟨q, hsfin.mem_toFinset.mpr hqs, hpq⟩

def diskBoundaryNet (n k : ℕ) : Finset Coord :=
  Classical.choose (exists_finite_disk_boundary_net n k)

theorem diskBoundaryNet_mem_frontier (n k : ℕ) {p : Coord} (hp : p ∈ diskBoundaryNet n k) :
    p ∈ frontier (accumulatingDisk n) :=
  (Classical.choose_spec (exists_finite_disk_boundary_net n k)).1 p hp

theorem diskBoundaryNet_cover (n k : ℕ) {p : Coord} (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ q ∈ diskBoundaryNet n k, dist p q < accumulatingScale k :=
  (Classical.choose_spec (exists_finite_disk_boundary_net n k)).2 p hp

def exteriorCenterNet (n k : ℕ) : Finset Coord := by
  classical
  exact (diskBoundaryNet n k).image (exteriorMiddleLift n k)

theorem exteriorCenterNet_mem_layer (n k : ℕ) {p : Coord} (hp : p ∈ exteriorCenterNet n k) :
    p ∈ exteriorOpenLayer n k := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact exteriorMiddleLift_mem_layer n k (diskBoundaryNet_mem_frontier n k hq)

theorem roundClosedDisk_sub_norm_le (c : Coord) {r : ℝ} (hr : 0 ≤ r)
    {p : Coord} (hp : p ∈ roundClosedDisk c r) : ‖p - c‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using roundClosedDisk_coord_abs_le c hr hp i

theorem dist_radialLift_self (c p : Coord) (s : ℝ) :
    dist (radialLift c s p) p = |s - 1| * ‖p - c‖ := by
  rw [dist_eq_norm]
  have hv : radialLift c s p - p = (s - 1) • (p - c) := by
    funext i
    simp only [radialLift, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv, norm_smul, Real.norm_eq_abs]

theorem exteriorMiddleLift_dist_le (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    dist (exteriorMiddleLift n k p) p ≤ accumulatingScale k * accumulatingRadius n := by
  have hdisk : p ∈ accumulatingDisk n := by
    have := (frontier_subset_closure : frontier (accumulatingDisk n) ⊆ closure (accumulatingDisk n)) hp
    simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using this
  have hnorm := roundClosedDisk_sub_norm_le (accumulatingCenter n)
    (accumulatingRadius_pos n).le hdisk
  have ha := accumulatingScale_pos k
  have hr := accumulatingRadius_pos n
  have hcoeff : 0 ≤ 1 + (7 / 8 : ℝ) * accumulatingScale k - 1 := by linarith
  rw [exteriorMiddleLift, dist_radialLift_self, abs_of_nonneg hcoeff]
  have hmul := mul_le_mul_of_nonneg_left hnorm hcoeff
  nlinarith [mul_pos ha hr]

theorem exteriorCenterNet_cover (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ q ∈ exteriorCenterNet n k,
      dist p q < (1 + accumulatingRadius n) * accumulatingScale k := by
  classical
  obtain ⟨v, hv, hpv⟩ := diskBoundaryNet_cover n k hp
  refine ⟨exteriorMiddleLift n k v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
  have hlift := exteriorMiddleLift_dist_le n k (diskBoundaryNet_mem_frontier n k hv)
  have htri := dist_triangle p v (exteriorMiddleLift n k v)
  rw [dist_comm v (exteriorMiddleLift n k v)] at htri
  nlinarith

theorem every_boundary_point_has_finite_net_sequence (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ centers : ℕ → Coord, (∀ k, centers k ∈ exteriorCenterNet n k) ∧
      Tendsto centers atTop (𝓝 p) := by
  classical
  have hchoose (k : ℕ) : ∃ q ∈ exteriorCenterNet n k,
      dist p q < (1 + accumulatingRadius n) * accumulatingScale k :=
    exteriorCenterNet_cover n k hp
  choose centers hcenters hdist using hchoose
  refine ⟨centers, hcenters, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (k : ℕ) : dist (centers k) p ≤
      (1 + accumulatingRadius n) * accumulatingScale k := by
    simpa only [dist_comm] using (hdist k).le
  apply squeeze_zero (fun _ => dist_nonneg) hbound
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := 1 + accumulatingRadius n)).mul tendsto_accumulatingScale

theorem exteriorClosedLayer_disjoint_every_disk (n k m : ℕ) :
    Disjoint (exteriorClosedLayer n k) (accumulatingDisk m) := by
  by_cases hnm : n = m
  · subst m
    exact exteriorClosedLayer_outside_disk n k
  · exact (enlargedAccumulatingDisks_pairwise_disjoint hnm).mono
      (exteriorClosedLayer_subset_enlarged n k) (accumulatingDisk_subset_enlarged m)

theorem exteriorCenterNet_avoids_every_disk (n k : ℕ) {p : Coord}
    (hp : p ∈ exteriorCenterNet n k) (m : ℕ) : p ∉ accumulatingDisk m := by
  intro hm
  exact Set.disjoint_left.mp (exteriorClosedLayer_disjoint_every_disk n k m)
    (exteriorOpenLayer_subset_closed n k (exteriorCenterNet_mem_layer n k hp)) hm

end SmoothLocal.Geometry

end

end OAI
