import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Coordinates for a bottom pair of the finite-field tree

The change of variables in §6 sends `(d,t)` to `(dt/(t-1),d/(t-1))`.
On its valid domain this is a bijection with the ordered distinct nonzero
pairs. It is the change of variables used in the bottom-pair second moment.
-/

namespace Ostmann

variable {K : Type*} [Field K]

def ValidPairCoordinates (K : Type*) [Field K] :=
  {dt : K × K // dt.1 ≠ 0 ∧ dt.2 ≠ 0 ∧ dt.2 ≠ 1}

def DistinctNonzeroPair (K : Type*) [Field K] :=
  {xz : K × K // xz.1 ≠ 0 ∧ xz.2 ≠ 0 ∧ xz.1 ≠ xz.2}

theorem pair_coordinate_difference (d t : K) (ht : t ≠ 1) :
    d * t / (t - 1) - d / (t - 1) = d := by
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp

theorem pair_coordinate_ratio (d t : K) (hd : d ≠ 0) (ht : t ≠ 1) :
    (d * t / (t - 1)) / (d / (t - 1)) = t := by
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp

theorem pair_coordinates_reconstruct (x z : K) (hz : z ≠ 0) (hxz : x ≠ z) :
    ((x - z) * (x / z) / (x / z - 1), (x - z) / (x / z - 1)) = (x, z) := by
  have hden : x / z - 1 ≠ 0 := by
    intro h
    have : x / z = 1 := sub_eq_zero.mp h
    exact hxz ((div_eq_one_iff_eq hz).mp this)
  have hsub : x - z ≠ 0 := sub_ne_zero.mpr hxz
  apply Prod.ext <;> dsimp
  · field_simp [hsub]
  · field_simp [hsub]

/-- The difference and ratio coordinates parametrize exactly the ordered
distinct nonzero pairs. -/
noncomputable def pairCoordinatesEquiv (K : Type*) [Field K] :
    ValidPairCoordinates K ≃ DistinctNonzeroPair K where
  toFun dt := ⟨(dt.1.1 * dt.1.2 / (dt.1.2 - 1), dt.1.1 / (dt.1.2 - 1)), by
    have hd := dt.2.1
    have ht := dt.2.2.1
    have hden := sub_ne_zero.mpr dt.2.2.2
    refine ⟨div_ne_zero (mul_ne_zero hd ht) hden, div_ne_zero hd hden, ?_⟩
    intro heq
    dsimp only at heq
    have hdifference := pair_coordinate_difference dt.1.1 dt.1.2 dt.2.2.2
    rw [heq, sub_self] at hdifference
    exact hd hdifference.symm⟩
  invFun xz := ⟨(xz.1.1 - xz.1.2, xz.1.1 / xz.1.2), by
    refine ⟨sub_ne_zero.mpr xz.2.2.2, div_ne_zero xz.2.1 xz.2.2.1, ?_⟩
    intro heq
    exact xz.2.2.2 ((div_eq_one_iff_eq xz.2.2.1).mp heq)⟩
  left_inv dt := by
    apply Subtype.ext
    exact Prod.ext (pair_coordinate_difference dt.1.1 dt.1.2 dt.2.2.2)
      (pair_coordinate_ratio dt.1.1 dt.1.2 dt.2.1 dt.2.2.2)
  right_inv xz := by
    apply Subtype.ext
    exact pair_coordinates_reconstruct xz.1.1 xz.1.2 xz.2.2.1 xz.2.2.2

end Ostmann

end OAI
