import OAI.Geometry.IsometricImmersion.Coordinates.AffinePatchSquares

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem exists_orientedPatchScale (n k : ℕ) (R : OrientationLabel) :
    ∃ scale > 0, scale ≤ accumulatingScale k ∧
      (∀ c ∈ orientedExteriorCenters n k R, closedAffineSquare c scale R.val ⊆
        exteriorOpenLayer n (orientedLayerIndex k R)) ∧
      (∀ c ∈ orientedExteriorCenters n k R, ∀ d ∈ orientedExteriorCenters n k R,
        c ≠ d → Disjoint (closedAffineSquare c scale R.val) (closedAffineSquare d scale R.val)) ∧
      ∀ c ∈ orientedExteriorCenters n k R, ∀ p ∈ closedAffineSquare c scale R.val,
        dist p c ≤ accumulatingScale k :=
  exists_finset_affine_square_scale (orientedExteriorCenters n k R)
    (exteriorOpenLayer_isOpen n (orientedLayerIndex k R))
    (fun _ hc => orientedExteriorCenters_mem_layer n k R hc) R.val (accumulatingScale_pos k)

def orientedPatchScale (n k : ℕ) (R : OrientationLabel) : ℝ :=
  Classical.choose (exists_orientedPatchScale n k R)

def orientedClosedPatch (n k : ℕ) (R : OrientationLabel) (c : Coord) : Set Coord :=
  closedAffineSquare c (orientedPatchScale n k R) R.val

theorem orientedPatchScale_pos (n k : ℕ) (R : OrientationLabel) :
    0 < orientedPatchScale n k R :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).1

theorem orientedPatchScale_le (n k : ℕ) (R : OrientationLabel) :
    orientedPatchScale n k R ≤ accumulatingScale k :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.1

theorem orientedClosedPatch_subset_layer (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ exteriorOpenLayer n (orientedLayerIndex k R) :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.2.1 c hc

theorem orientedClosedPatch_dist_le (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R)
    {p : Coord} (hp : p ∈ orientedClosedPatch n k R c) :
    dist p c ≤ accumulatingScale k :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.2.2.2 c hc p hp

theorem orientedClosedPatch_isCompact (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    IsCompact (orientedClosedPatch n k R c) :=
  closedAffineSquare_isCompact c (orientedPatchScale n k R) R.val

theorem center_mem_orientedClosedPatch (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    c ∈ orientedClosedPatch n k R c :=
  center_mem_closedAffineSquare c (orientedPatchScale n k R) R.val

theorem orientedClosedPatches_disjoint_same_layer (n k : ℕ) (R : OrientationLabel)
    {c d : Coord} (hc : c ∈ orientedExteriorCenters n k R)
    (hd : d ∈ orientedExteriorCenters n k R) (hcd : c ≠ d) :
    Disjoint (orientedClosedPatch n k R c) (orientedClosedPatch n k R d) :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.2.2.1 c hc d hd hcd

theorem orientedClosedPatch_subset_closedLayer (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ exteriorClosedLayer n (orientedLayerIndex k R) :=
  (orientedClosedPatch_subset_layer n k R hc).trans
    (exteriorOpenLayer_subset_closed n (orientedLayerIndex k R))

theorem orientedClosedPatches_disjoint_different_layers (n : ℕ)
    {a b : ℕ × OrientationLabel} (hab : a ≠ b) {c d : Coord}
    (hc : c ∈ orientedExteriorCenters n a.1 a.2)
    (hd : d ∈ orientedExteriorCenters n b.1 b.2) :
    Disjoint (orientedClosedPatch n a.1 a.2 c) (orientedClosedPatch n b.1 b.2 d) :=
  (orientedExteriorLayers_disjoint n hab).mono
    (orientedClosedPatch_subset_closedLayer n a.1 a.2 hc)
    (orientedClosedPatch_subset_closedLayer n b.1 b.2 hd)

theorem orientedClosedPatches_disjoint_different_disks {n m : ℕ} (hnm : n ≠ m)
    (k l : ℕ) (R S : OrientationLabel) {c d : Coord}
    (hc : c ∈ orientedExteriorCenters n k R)
    (hd : d ∈ orientedExteriorCenters m l S) :
    Disjoint (orientedClosedPatch n k R c) (orientedClosedPatch m l S d) :=
  (exteriorClosedLayers_disjoint_different_disks hnm (orientedLayerIndex k R)
    (orientedLayerIndex l S)).mono (orientedClosedPatch_subset_closedLayer n k R hc)
      (orientedClosedPatch_subset_closedLayer m l S hd)

theorem orientedClosedPatch_disjoint_every_disk (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) (m : ℕ) :
    Disjoint (orientedClosedPatch n k R c) (accumulatingDisk m) :=
  (exteriorClosedLayer_disjoint_every_disk n (orientedLayerIndex k R) m).mono_left
    (orientedClosedPatch_subset_closedLayer n k R hc)

theorem orientedClosedPatch_subset_enlarged (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ enlargedAccumulatingDisk n :=
  (orientedClosedPatch_subset_closedLayer n k R hc).trans
    (exteriorClosedLayer_subset_enlarged n (orientedLayerIndex k R))

theorem orientedClosedPatch_subset_square (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ square :=
  (orientedClosedPatch_subset_enlarged n k R hc).trans (enlargedAccumulatingDisk_subset_square n)

theorem orientedPatchScale_tendsto (n : ℕ) (R : OrientationLabel) :
    Tendsto (fun k => orientedPatchScale n k R) atTop (𝓝 0) :=
  squeeze_zero (fun k => (orientedPatchScale_pos n k R).le)
    (fun k => orientedPatchScale_le n k R) tendsto_accumulatingScale

theorem orientedPatchMatrix_isUnit (n k : ℕ) (R : OrientationLabel) :
    IsUnit (orientedPatchScale n k R • R.val) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_smul, (orientationRotations_properties R.property).2.2]
  exact mul_ne_zero (pow_ne_zero _ (orientedPatchScale_pos n k R).ne') one_ne_zero

theorem every_boundary_point_every_orientation_patch_neighborhoods (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) (R : OrientationLabel) :
    ∃ centers : ℕ → Coord,
      (∀ k, centers k ∈ orientedExteriorCenters n k R) ∧
      Tendsto centers atTop (𝓝 p) ∧
      ∀ V ∈ 𝓝 p, ∀ᶠ k in atTop, orientedClosedPatch n k R (centers k) ⊆ V := by
  obtain ⟨centers, hcenters, ht⟩ := every_boundary_point_every_orientation_centers n p hp R
  refine ⟨centers, hcenters, ht, ?_⟩
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hsmall : Tendsto (fun k => accumulatingScale k + dist (centers k) p) atTop (𝓝 0) := by
    simpa only [dist_self, add_zero] using tendsto_accumulatingScale.add
      (ht.dist (tendsto_const_nhds (x := p)))
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with k hk
  intro q hq
  apply hball
  exact lt_of_le_of_lt ((dist_triangle q (centers k) p).trans
    (add_le_add (orientedClosedPatch_dist_le n k R (hcenters k) hq) le_rfl)) hk

end SmoothLocal.Geometry

end

end OAI
