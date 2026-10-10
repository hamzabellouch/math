import OAI.Geometry.IsometricImmersion.Assembly.AccumulatingDisks
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry

theorem roundRadiusSq_contDiff (c : Coord) : ContDiff ℝ ∞ (roundRadiusSq c) :=
  (((contDiff_apply ℝ ℝ 0).sub contDiff_const).pow 2).add
    (((contDiff_apply ℝ ℝ 1).sub contDiff_const).pow 2)

def negativeDiskProfile (c : Coord) (r : ℝ) (p : Coord) : ℝ :=
  -expNegInvGlue (r ^ 2 - roundRadiusSq c p)

theorem negativeDiskProfile_contDiff (c : Coord) (r : ℝ) :
    ContDiff ℝ ∞ (negativeDiskProfile c r) :=
  (expNegInvGlue.contDiff.comp (contDiff_const.sub (roundRadiusSq_contDiff c))).neg

theorem negativeDiskProfile_nonpos (c : Coord) (r : ℝ) (p : Coord) :
    negativeDiskProfile c r p ≤ 0 := neg_nonpos.mpr (expNegInvGlue.nonneg _)

theorem negativeDiskProfile_neg_inside (c : Coord) (r : ℝ) {p : Coord}
    (hp : p ∈ roundOpenDisk c r) : negativeDiskProfile c r p < 0 :=
  neg_neg_of_pos (expNegInvGlue.pos_of_pos (sub_pos.mpr hp))

theorem negativeDiskProfile_zero_outside (c : Coord) (r : ℝ) {p : Coord}
    (hp : p ∉ roundOpenDisk c r) : negativeDiskProfile c r p = 0 := by
  have hle : r ^ 2 ≤ roundRadiusSq c p := le_of_not_gt hp
  simp only [negativeDiskProfile, expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hle), neg_zero]

theorem negativeDiskProfile_support (c : Coord) (r : ℝ) :
    Function.support (negativeDiskProfile c r) = roundOpenDisk c r := by
  ext p
  constructor
  · intro hp
    by_contra hnot
    exact hp (negativeDiskProfile_zero_outside c r hnot)
  · intro hp
    exact (negativeDiskProfile_neg_inside c r hp).ne

theorem negativeDiskProfile_tsupport_subset (c : Coord) {r : ℝ} (hr : 0 < r) :
    tsupport (negativeDiskProfile c r) ⊆ roundClosedDisk c r := by
  apply closure_minimal _ (isCompact_roundClosedDisk c hr).isClosed
  rw [negativeDiskProfile_support]
  exact fun p hp => (show roundRadiusSq c p < r^2 from hp).le

theorem negativeDiskProfile_hasCompactSupport (c : Coord) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (negativeDiskProfile c r) :=
  (isCompact_roundClosedDisk c hr).of_isClosed_subset (isClosed_tsupport _)
    (negativeDiskProfile_tsupport_subset c hr)

theorem negativeDiskProfile_frontier_zero (c : Coord) {r : ℝ} (hr : 0 < r)
    {p : Coord} (hp : p ∈ frontier (roundClosedDisk c r)) :
    negativeDiskProfile c r p = 0 := by
  have heq := (mem_frontier_roundClosedDisk_iff c p hr).mp hp
  simp only [negativeDiskProfile, heq, sub_self, expNegInvGlue.zero, neg_zero]

def accumulatingDiskProfile (n : ℕ) : Coord → ℝ :=
  negativeDiskProfile (accumulatingCenter n) (accumulatingRadius n)

theorem accumulatingDiskProfile_contDiff (n : ℕ) : ContDiff ℝ ∞ (accumulatingDiskProfile n) :=
  negativeDiskProfile_contDiff _ _

theorem accumulatingDiskProfile_tsupport_subset (n : ℕ) :
    tsupport (accumulatingDiskProfile n) ⊆ accumulatingDisk n :=
  negativeDiskProfile_tsupport_subset _ (accumulatingRadius_pos n)

theorem accumulatingDiskProfile_hasCompactSupport (n : ℕ) :
    HasCompactSupport (accumulatingDiskProfile n) :=
  negativeDiskProfile_hasCompactSupport _ (accumulatingRadius_pos n)

theorem accumulatingDiskProfile_neg_interior (n : ℕ) {p : Coord}
    (hp : p ∈ interior (accumulatingDisk n)) : accumulatingDiskProfile n p < 0 := by
  apply negativeDiskProfile_neg_inside
  simpa only [accumulatingDisk,
    interior_roundClosedDisk _ (accumulatingRadius_pos n)] using hp

theorem accumulatingDiskProfile_frontier_zero (n : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) : accumulatingDiskProfile n p = 0 :=
  negativeDiskProfile_frontier_zero _ (accumulatingRadius_pos n) hp

end SmoothLocal.Geometry

end

end OAI
