import OAI.Geometry.IsometricImmersion.Assembly.AccumulatingDisks

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def roundDistance (c p : Coord) : ℝ :=
  dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates c)

theorem roundDistance_sq (c p : Coord) : roundDistance c p ^ 2 = roundRadiusSq c p :=
  euclideanPlaneCoordinates_dist_sq p c

theorem roundDistance_nonneg (c p : Coord) : 0 ≤ roundDistance c p := dist_nonneg

theorem roundDistance_continuous (c : Coord) : Continuous (roundDistance c) :=
  euclideanPlaneCoordinates.continuous.dist continuous_const

theorem mem_roundClosedDisk_iff_roundDistance (c p : Coord) {r : ℝ} (hr : 0 ≤ r) :
    p ∈ roundClosedDisk c r ↔ roundDistance c p ≤ r := by
  rw [roundClosedDisk_eq_preimage_closedBall c hr]
  rfl

theorem mem_roundOpenDisk_iff_roundDistance (c p : Coord) {r : ℝ} (hr : 0 ≤ r) :
    p ∈ roundOpenDisk c r ↔ roundDistance c p < r := by
  rw [roundOpenDisk_eq_preimage_ball c hr]
  rfl

theorem frontier_roundDistance_eq (c p : Coord) {r : ℝ} (hr : 0 < r)
    (hp : p ∈ frontier (roundClosedDisk c r)) : roundDistance c p = r := by
  apply (sq_eq_sq₀ (roundDistance_nonneg c p) hr.le).mp
  rw [roundDistance_sq]
  exact (mem_frontier_roundClosedDisk_iff c p hr).mp hp

def exteriorLayerInner (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + (3 / 4 : ℝ) * accumulatingScale k)

def exteriorLayerOuter (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + accumulatingScale k)

def exteriorLayerMiddle (n k : ℕ) : ℝ :=
  accumulatingRadius n * (1 + (7 / 8 : ℝ) * accumulatingScale k)

def exteriorClosedLayer (n k : ℕ) : Set Coord := {p |
  exteriorLayerInner n k ≤ roundDistance (accumulatingCenter n) p ∧
    roundDistance (accumulatingCenter n) p ≤ exteriorLayerOuter n k}

def exteriorOpenLayer (n k : ℕ) : Set Coord := {p |
  exteriorLayerInner n k < roundDistance (accumulatingCenter n) p ∧
    roundDistance (accumulatingCenter n) p < exteriorLayerOuter n k}

theorem exteriorLayer_radii (n k : ℕ) :
    accumulatingRadius n < exteriorLayerInner n k ∧
      exteriorLayerInner n k < exteriorLayerMiddle n k ∧
      exteriorLayerMiddle n k < exteriorLayerOuter n k ∧
      exteriorLayerOuter n k < 2 * accumulatingRadius n := by
  have hr := accumulatingRadius_pos n
  have ha := accumulatingScale_pos k
  have hab := accumulatingScale_le_half k
  have hra := mul_pos hr ha
  unfold exteriorLayerInner exteriorLayerMiddle exteriorLayerOuter
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exteriorLayer_clearances (n k : ℕ) :
    exteriorLayerInner n k - accumulatingRadius n =
        (3 / 4 : ℝ) * accumulatingRadius n * accumulatingScale k ∧
      2 * accumulatingRadius n - exteriorLayerOuter n k =
        accumulatingRadius n * (1 - accumulatingScale k) ∧
      exteriorLayerMiddle n k - exteriorLayerInner n k =
        accumulatingRadius n * accumulatingScale k / 8 ∧
      exteriorLayerOuter n k - exteriorLayerMiddle n k =
        accumulatingRadius n * accumulatingScale k / 8 := by
  simp only [exteriorLayerInner, exteriorLayerMiddle, exteriorLayerOuter]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem exteriorOpenLayer_isOpen (n k : ℕ) : IsOpen (exteriorOpenLayer n k) :=
  (isOpen_lt continuous_const (roundDistance_continuous _)).inter
    (isOpen_lt (roundDistance_continuous _) continuous_const)

theorem exteriorClosedLayer_isClosed (n k : ℕ) : IsClosed (exteriorClosedLayer n k) :=
  (isClosed_le continuous_const (roundDistance_continuous _)).inter
    (isClosed_le (roundDistance_continuous _) continuous_const)

theorem exteriorOpenLayer_subset_closed (n k : ℕ) :
    exteriorOpenLayer n k ⊆ exteriorClosedLayer n k := fun _ hp => ⟨hp.1.le, hp.2.le⟩

theorem exteriorClosedLayer_outside_disk (n k : ℕ) :
    Disjoint (exteriorClosedLayer n k) (accumulatingDisk n) := by
  apply Set.disjoint_left.mpr
  intro p hp hd
  have hrad := (mem_roundClosedDisk_iff_roundDistance _ _ (accumulatingRadius_pos n).le).mp hd
  have hlo := (exteriorLayer_radii n k).1
  exact (not_le_of_gt hlo) (hp.1.trans hrad)

theorem exteriorClosedLayer_subset_enlarged_open (n k : ℕ) :
    exteriorClosedLayer n k ⊆
      roundOpenDisk (accumulatingCenter n) (2 * accumulatingRadius n) := by
  intro p hp
  apply (mem_roundOpenDisk_iff_roundDistance _ _
    (mul_pos (by norm_num) (accumulatingRadius_pos n)).le).mpr
  exact hp.2.trans_lt (exteriorLayer_radii n k).2.2.2

theorem exteriorClosedLayer_subset_enlarged (n k : ℕ) :
    exteriorClosedLayer n k ⊆ enlargedAccumulatingDisk n := by
  intro p hp
  apply (mem_roundClosedDisk_iff_roundDistance _ _
    (mul_pos (by norm_num) (accumulatingRadius_pos n)).le).mpr
  exact (hp.2.trans_lt (exteriorLayer_radii n k).2.2.2).le

theorem exteriorClosedLayer_isCompact (n k : ℕ) : IsCompact (exteriorClosedLayer n k) :=
  (enlargedAccumulatingDisk_isCompact n).of_isClosed_subset
    (exteriorClosedLayer_isClosed n k) (exteriorClosedLayer_subset_enlarged n k)

theorem exteriorLayer_separated {k l : ℕ} (n : ℕ) (hkl : k < l) :
    exteriorLayerOuter n l < exteriorLayerInner n k := by
  have ha := accumulatingScale_le_half_of_lt hkl
  have hpos := mul_pos (accumulatingRadius_pos n) (accumulatingScale_pos k)
  have hmul := mul_le_mul_of_nonneg_left ha (accumulatingRadius_pos n).le
  unfold exteriorLayerOuter exteriorLayerInner
  nlinarith

theorem exteriorClosedLayers_pairwise_disjoint (n : ℕ) :
    Pairwise (fun k l => Disjoint (exteriorClosedLayer n k) (exteriorClosedLayer n l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro p hp hk
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact (not_le_of_gt (exteriorLayer_separated n hlt)) (hp.1.trans hk.2)
  · exact (not_le_of_gt (exteriorLayer_separated n hgt)) (hk.1.trans hp.2)

theorem exteriorClosedLayers_disjoint_different_disks {n m : ℕ}
    (hnm : n ≠ m) (k l : ℕ) : Disjoint (exteriorClosedLayer n k) (exteriorClosedLayer m l) :=
  (enlargedAccumulatingDisks_pairwise_disjoint hnm).mono
    (exteriorClosedLayer_subset_enlarged n k) (exteriorClosedLayer_subset_enlarged m l)

def radialLift (c : Coord) (s : ℝ) (p : Coord) : Coord := c + s • (p - c)

theorem roundDistance_radialLift (c p : Coord) (s : ℝ) :
    roundDistance c (radialLift c s p) = |s| * roundDistance c p := by
  simp only [roundDistance, radialLift, dist_eq_norm, map_add, map_smul, map_sub,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

def exteriorMiddleLift (n k : ℕ) (p : Coord) : Coord :=
  radialLift (accumulatingCenter n) (1 + (7 / 8 : ℝ) * accumulatingScale k) p

theorem exteriorMiddleLift_mem_layer (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    exteriorMiddleLift n k p ∈ exteriorOpenLayer n k := by
  have hr := frontier_roundDistance_eq (accumulatingCenter n) p (accumulatingRadius_pos n) hp
  have hs : 0 ≤ 1 + (7 / 8 : ℝ) * accumulatingScale k := by
    have := accumulatingScale_pos k
    positivity
  have hrad : roundDistance (accumulatingCenter n) (exteriorMiddleLift n k p) =
      exteriorLayerMiddle n k := by
    rw [exteriorMiddleLift, roundDistance_radialLift, abs_of_nonneg hs, hr]
    unfold exteriorLayerMiddle
    ring
  change exteriorLayerInner n k < _ ∧ _ < exteriorLayerOuter n k
  rw [hrad]
  exact ⟨(exteriorLayer_radii n k).2.1, (exteriorLayer_radii n k).2.2.1⟩

theorem exteriorMiddleLift_tendsto (n : ℕ) (p : Coord) :
    Tendsto (fun k => exteriorMiddleLift n k p) atTop (𝓝 p) := by
  have ht : Tendsto (fun k => 1 + (7 / 8 : ℝ) * accumulatingScale k) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add ((tendsto_const_nhds (x := (7 / 8 : ℝ))).mul tendsto_accumulatingScale)
  have h := (tendsto_const_nhds (x := accumulatingCenter n)).add
    (ht.smul_const (p - accumulatingCenter n))
  have he : accumulatingCenter n+(p-accumulatingCenter n) = p := by abel
  simp only [one_smul,he] at h
  exact h

theorem every_disk_boundary_has_exterior_layer_sequence (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ centers : ℕ → Coord, (∀ k, centers k ∈ exteriorOpenLayer n k) ∧
      Tendsto centers atTop (𝓝 p) :=
  ⟨fun k => exteriorMiddleLift n k p, fun k => exteriorMiddleLift_mem_layer n k hp,
    exteriorMiddleLift_tendsto n p⟩

end SmoothLocal.Geometry

end

end OAI
