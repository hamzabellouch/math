import OAI.Geometry.SurfaceImmersion.Geometry.TransverseJetConvexity

namespace OAI

/-! The simplest affine coefficient with the two prescribed endpoint signs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def nonzeroSign (r : ℝ) : ℝ := if 0 < r then 1 else -1

def endpointSignModel (p q a b t : ℝ) : ℝ :=
  ((q-t)/(q-p))*nonzeroSign a+((t-p)/(q-p))*nonzeroSign b

lemma nonzeroSign_mul_pos {r : ℝ} (hr : r ≠ 0) : 0 < r*nonzeroSign r := by
  by_cases hp : 0 < r
  · simp [nonzeroSign,hp]
  · have hn : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
    simp [nonzeroSign,hp,hn]

lemma endpointSignModel_left {p q a b : ℝ} (hpq : p ≠ q) :
    endpointSignModel p q a b p = nonzeroSign a := by
  simp [endpointSignModel,sub_ne_zero.mpr hpq.symm]

lemma endpointSignModel_right {p q a b : ℝ} (hpq : p ≠ q) :
    endpointSignModel p q a b q = nonzeroSign b := by
  simp [endpointSignModel,sub_ne_zero.mpr hpq.symm]

lemma endpointSignModel_smooth (p q a b : ℝ) :
    ContDiff ℝ ∞ (endpointSignModel p q a b) := by
  unfold endpointSignModel
  fun_prop

lemma endpointSignModel_left_mul_pos {p q a b : ℝ} (hpq : p ≠ q) (ha : a ≠ 0) :
    0 < a*endpointSignModel p q a b p := by
  rw [endpointSignModel_left hpq]
  exact nonzeroSign_mul_pos ha

lemma endpointSignModel_right_mul_pos {p q a b : ℝ} (hpq : p ≠ q) (hb : b ≠ 0) :
    0 < b*endpointSignModel p q a b q := by
  rw [endpointSignModel_right hpq]
  exact nonzeroSign_mul_pos hb

lemma endpointSignModel_same {p q a b : ℝ} (hpq : p ≠ q)
    (hsame : nonzeroSign a = nonzeroSign b) (t : ℝ) :
    endpointSignModel p q a b t = nonzeroSign a := by
  unfold endpointSignModel
  rw [←hsame]
  field_simp [sub_ne_zero.mpr hpq.symm]
  ring

lemma endpointSignModel_opposite {p q a b : ℝ} (hpq : p ≠ q)
    (hopp : nonzeroSign b = -nonzeroSign a) (t : ℝ) :
    endpointSignModel p q a b t = ((p+q-2*t)/(q-p))*nonzeroSign a := by
  unfold endpointSignModel
  rw [hopp]
  field_simp [sub_ne_zero.mpr hpq.symm]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
