import OAI.Geometry.IsometricImmersion.Coordinates.OrientedPatchSquares
import OAI.Geometry.IsometricImmersion.Coordinates.AffinePushforward
import OAI.Geometry.IsometricImmersion.Metrics.ModelProfile
import OAI.Geometry.IsometricImmersion.Caps.EllipticCutoff

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter Metric

namespace SmoothLocal.Geometry
open SmoothLocal.Weighted SmoothLocal.Model

def openPatchBox : Set Coord := {x | ∀ i, x i ∈ Set.Ioo (-4 : ℝ) 4}

theorem mem_openPatchBox_iff_norm_lt (x : Coord) :
    x ∈ openPatchBox ↔ ‖x‖ < 4 := by
  rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 4)]
  simp only [openPatchBox, Set.mem_ofPred_eq, Set.mem_Ioo, Real.norm_eq_abs, abs_lt]

theorem openPatchBox_subset_closedPatchBox : openPatchBox ⊆ closedPatchBox := by
  intro x hx i
  exact ⟨(hx i).1.le, (hx i).2.le⟩

def patchAxisCutoff (x : ℝ) : ℝ :=
  intervalCutoff (-(15 / 4 : ℝ)) (-(13 / 4 : ℝ)) x *
    intervalCutoff (-(15 / 4 : ℝ)) (-(13 / 4 : ℝ)) (-x)

theorem patchAxisCutoff_contDiff : ContDiff ℝ ∞ patchAxisCutoff :=
  (intervalCutoff_contDiff _ _).mul ((intervalCutoff_contDiff _ _).comp contDiff_id.neg)

theorem patchAxisCutoff_one {x : ℝ} (hx : |x| ≤ 13 / 4) : patchAxisCutoff x = 1 := by
  have hlo := (abs_le.mp hx).1
  have hhi := (abs_le.mp hx).2
  rw [patchAxisCutoff, intervalCutoff_one (by norm_num) hlo,
    intervalCutoff_one (by norm_num) (show -(13 / 4 : ℝ) ≤ -x by linarith)]
  norm_num

theorem patchAxisCutoff_zero_left {x : ℝ} (hx : x ≤ -(15 / 4 : ℝ)) :
    patchAxisCutoff x = 0 := by
  simp only [patchAxisCutoff, intervalCutoff_zero (b := -(13 / 4 : ℝ))
    (by norm_num) hx, zero_mul]

theorem patchAxisCutoff_zero_right {x : ℝ} (hx : 15 / 4 ≤ x) :
    patchAxisCutoff x = 0 := by
  simp only [patchAxisCutoff, intervalCutoff_zero (b := -(13 / 4 : ℝ)) (by norm_num)
    (show -x ≤ -(15 / 4 : ℝ) by linarith), mul_zero]

theorem patchAxisCutoff_support_bound {x : ℝ} (hx : patchAxisCutoff x ≠ 0) :
    |x| < 15 / 4 := by
  apply abs_lt.mpr
  constructor
  · by_contra h
    exact hx (patchAxisCutoff_zero_left (le_of_not_gt h))
  · by_contra h
    exact hx (patchAxisCutoff_zero_right (le_of_not_gt h))

def patchBoxCutoff (p : Coord) : ℝ := patchAxisCutoff (p 0) * patchAxisCutoff (p 1)

theorem patchBoxCutoff_contDiff : ContDiff ℝ ∞ patchBoxCutoff :=
  (patchAxisCutoff_contDiff.comp (contDiff_apply ℝ ℝ 0)).mul
    (patchAxisCutoff_contDiff.comp (contDiff_apply ℝ ℝ 1))

theorem patchBoxCutoff_one {p : Coord} (hp : ‖p‖ ≤ 13 / 4) : patchBoxCutoff p = 1 := by
  have hb (i : Fin 2) : |p i| ≤ 13 / 4 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm p i).trans hp
  simp only [patchBoxCutoff, patchAxisCutoff_one (hb 0), patchAxisCutoff_one (hb 1), one_mul]

theorem patchBoxCutoff_support_bound {p : Coord} (hp : patchBoxCutoff p ≠ 0) :
    ‖p‖ < 15 / 4 := by
  have hprod := mul_ne_zero_iff.mp hp
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 15 / 4)).mpr
  intro i
  fin_cases i
  · change |p 0| < 15 / 4
    exact patchAxisCutoff_support_bound hprod.1
  · change |p 1| < 15 / 4
    exact patchAxisCutoff_support_bound hprod.2

def localPatchProfile (p : Coord) : ℝ := patchBoxCutoff p * modelCurvature 1 p

theorem localPatchProfile_contDiff : ContDiff ℝ ∞ localPatchProfile :=
  patchBoxCutoff_contDiff.mul (modelCurvature_contDiff 1)

theorem localPatchProfile_eq_model {p : Coord} (hp : ‖p‖ ≤ 13 / 4) :
    localPatchProfile p = (p 0) ^ 2 - modelProfile (p 1) := by
  simp only [localPatchProfile, patchBoxCutoff_one hp, modelCurvature, one_mul]

theorem localPatchProfile_tsupport_bound :
    tsupport localPatchProfile ⊆ Metric.closedBall (0 : Coord) (15 / 4) := by
  apply closure_minimal _ isClosed_closedBall
  intro p hp
  have hcut : patchBoxCutoff p ≠ 0 := (mul_ne_zero_iff.mp hp).1
  change dist p 0 ≤ 15 / 4
  simpa only [dist_zero_right] using (patchBoxCutoff_support_bound hcut).le

theorem localPatchProfile_hasCompactSupport : HasCompactSupport localPatchProfile :=
  (isCompact_closedBall (0 : Coord) (15 / 4)).of_isClosed_subset
    (isClosed_tsupport _) localPatchProfile_tsupport_bound

theorem localPatchProfile_tsupport_strictly_inside : tsupport localPatchProfile ⊆ openPatchBox := by
  intro p hp
  apply (mem_openPatchBox_iff_norm_lt p).mpr
  have hnorm : ‖p‖ ≤ 15 / 4 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using localPatchProfile_tsupport_bound hp
  linarith

def affinePatchProfile (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord → ℝ :=
  localPatchProfile ∘ affineInverseCoordinates c R

theorem affinePatchProfile_contDiff (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affinePatchProfile c R) :=
  localPatchProfile_contDiff.comp (affineInverseCoordinates_contDiff c R)

theorem affinePatchProfile_support (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : Function.support (affinePatchProfile c R) =
      affineCoordinates c R '' Function.support localPatchProfile := by
  ext p
  constructor
  · intro hp
    exact ⟨affineInverseCoordinates c R p, hp,
      affineCoordinates_affineInverseCoordinates c R hR p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Function.mem_support, affinePatchProfile, Function.comp_apply,
      affineInverseCoordinates_affineCoordinates c R hR] using hq

theorem affinePatchProfile_tsupport (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : tsupport (affinePatchProfile c R) =
      affineCoordinates c R '' tsupport localPatchProfile := by
  rw [tsupport, affinePatchProfile_support c R hR]
  exact ((affineCoordinateHomeomorph c R hR).image_closure
    (Function.support localPatchProfile)).symm

theorem affinePatchProfile_hasCompactSupport (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    HasCompactSupport (affinePatchProfile c R) := by
  change IsCompact (tsupport (affinePatchProfile c R))
  rw [affinePatchProfile_tsupport c R hR]
  exact localPatchProfile_hasCompactSupport.image (affineCoordinates_contDiff c R).continuous

theorem affinePatchProfile_tsupport_strictly_inside (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    tsupport (affinePatchProfile c R) ⊆ affineCoordinates c R '' openPatchBox := by
  rw [affinePatchProfile_tsupport c R hR]
  exact Set.image_mono localPatchProfile_tsupport_strictly_inside

def patchModelNeighborhood (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) : Set Coord :=
  affineCoordinates c R '' Metric.ball (0 : Coord) (13 / 4)

theorem patchModelNeighborhood_isOpen (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : IsOpen (patchModelNeighborhood c R) :=
  (affineCoordinateHomeomorph c R hR).isOpenMap _ Metric.isOpen_ball

theorem patchModelNeighborhood_contains_innerSquare (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affineCoordinates c R '' {q : Coord | ∀ i, q i ∈ Icc (-3 : ℝ) 3} ⊆
      patchModelNeighborhood c R := by
  apply Set.image_mono
  intro q hq
  have hnorm : ‖q‖ ≤ 3 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
    intro i
    simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using hq i
  change dist q 0 < 13 / 4
  rw [dist_zero_right]
  linarith

theorem affinePatchProfile_eq_model_on_neighborhood (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    {p : Coord} (hp : p ∈ patchModelNeighborhood c R) :
    affinePatchProfile c R p = (affineInverseCoordinates c R p 0) ^ 2 -
      modelProfile (affineInverseCoordinates c R p 1) := by
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [affinePatchProfile, Function.comp_apply,
    affineInverseCoordinates_affineCoordinates c R hR]
  apply localPatchProfile_eq_model
  exact (show ‖q‖ < 13 / 4 by simpa only [Metric.mem_ball, dist_zero_right] using hq).le

def orientedPatchProfile (n k : ℕ) (R : OrientationLabel) (c : Coord) : Coord → ℝ :=
  affinePatchProfile c (orientedPatchScale n k R • R.val)

theorem orientedPatchProfile_contDiff (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    ContDiff ℝ ∞ (orientedPatchProfile n k R c) := affinePatchProfile_contDiff _ _

theorem orientedPatchProfile_hasCompactSupport (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    HasCompactSupport (orientedPatchProfile n k R c) :=
  affinePatchProfile_hasCompactSupport _ _ (orientedPatchMatrix_isUnit n k R)

theorem orientedPatchProfile_tsupport_subset_patch (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    tsupport (orientedPatchProfile n k R c) ⊆ orientedClosedPatch n k R c :=
  (affinePatchProfile_tsupport_strictly_inside c _ (orientedPatchMatrix_isUnit n k R)).trans
    (Set.image_mono openPatchBox_subset_closedPatchBox)

theorem orientedPatchProfile_tsupport_subset_layer (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    tsupport (orientedPatchProfile n k R c) ⊆ exteriorOpenLayer n (orientedLayerIndex k R) :=
  (orientedPatchProfile_tsupport_subset_patch n k R c).trans
    (orientedClosedPatch_subset_layer n k R hc)

end SmoothLocal.Geometry

end

end OAI
