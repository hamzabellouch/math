import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiGeometry

namespace OAI

/-! Actual rectangle dilations and containment of intersecting rectangles
with controlled relative angle, as used in Lacey--Li (3.4). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.Rectangle

def dilate (R : Rectangle) (a : ℝ) (ha : 0<a) : Rectangle where
  center := R.center
  axes := R.axes
  long := a*R.long
  short := a*R.short
  short_pos := mul_pos ha R.short_pos
  short_le_long := mul_le_mul_of_nonneg_left R.short_le_long ha.le

theorem mem_dilate (R : Rectangle) (a : ℝ) (ha : 0<a) (x : Plane) :
    x∈(R.dilate a ha).carrier ↔
      |R.axes.repr (x-R.center) 0| ≤ a*R.long/2 ∧
      |R.axes.repr (x-R.center) 1| ≤ a*R.short/2 := Iff.rfl

theorem carrier_subset_dilate (R : Rectangle) (a : ℝ) (ha : 1≤a) :
    R.carrier⊆(R.dilate a (lt_of_lt_of_le zero_lt_one ha)).carrier := by
  intro x hx
  constructor
  · change |R.axes.repr (x-R.center) 0| ≤ a*R.long/2
    exact hx.1.trans (by nlinarith [R.long_pos])
  · change |R.axes.repr (x-R.center) 1| ≤ a*R.short/2
    exact hx.2.trans (by nlinarith [R.short_pos])

theorem volume_dilate (R : Rectangle) (a : ℝ) (ha : 0<a) :
    volume (R.dilate a ha).carrier=ENNReal.ofReal (a^2)*volume R.carrier := by
  rw [volume_carrier,volume_carrier]
  simp only [dilate,ENNReal.ofReal_mul ha.le,ENNReal.ofReal_pow ha.le]
  ring

theorem abs_coordinate_le_norm (R : Rectangle) (x : Plane) (i : Fin 2) :
    |R.axes.repr x i|≤‖x‖ := by
  rw [R.axes.repr_apply_apply]
  simpa only [R.axes.norm_eq_one,one_mul] using abs_real_inner_le_norm (R.axes i) x

theorem coordinate_difference_zero (R : Rectangle) {x y : Plane}
    (hx : x∈R.carrier) (hy : y∈R.carrier) : |R.axes.repr (x-y) 0|≤R.long := by
  have he : R.axes.repr (x-y) 0=R.axes.repr (x-R.center) 0-R.axes.repr (y-R.center) 0 := by
    simp only [R.axes.repr_apply_apply,inner_sub_right]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hx.1,hy.1])

theorem coordinate_difference_one (R : Rectangle) {x y : Plane}
    (hx : x∈R.carrier) (hy : y∈R.carrier) : |R.axes.repr (x-y) 1|≤R.short := by
  have he : R.axes.repr (x-y) 1=R.axes.repr (x-R.center) 1-R.axes.repr (y-R.center) 1 := by
    simp only [R.axes.repr_apply_apply,inner_sub_right]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hx.2,hy.2])

theorem transverse_axis_le (R S : Rectangle) :
    |R.axes.repr (S.axes 0) 1|≤dist (R.axes 0) (S.axes 0) := by
  have hz : R.axes.repr (R.axes 0) 1=0 := by
    simp
  have h := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 1
  rw [map_sub,PiLp.sub_apply,hz,sub_zero] at h
  simpa only [dist_eq_norm,norm_sub_rev] using h

theorem transverse_difference_le (R S : Rectangle) {x y : Plane}
    (hx : x∈S.carrier) (hy : y∈S.carrier) :
    |R.axes.repr (x-y) 1|≤S.long*dist (R.axes 0) (S.axes 0)+S.short := by
  have he : R.axes.repr (x-y) 1=
      S.axes.repr (x-y) 0*R.axes.repr (S.axes 0) 1+
      S.axes.repr (x-y) 1*R.axes.repr (S.axes 1) 1 := by
    nth_rw 1 [←S.axes.sum_repr (x-y)]
    rw [Fin.sum_univ_two,map_add,PiLp.add_apply,map_smul,map_smul]
    rfl
  have hc := R.abs_coordinate_le_norm (S.axes 1) 1
  rw [S.axes.norm_eq_one] at hc
  rw [he]
  calc
    _ ≤ |S.axes.repr (x-y) 0| *|R.axes.repr (S.axes 0) 1|+
        |S.axes.repr (x-y) 1| *|R.axes.repr (S.axes 1) 1| := by
      simpa only [abs_mul] using abs_add_le
        (S.axes.repr (x-y) 0*R.axes.repr (S.axes 0) 1)
        (S.axes.repr (x-y) 1*R.axes.repr (S.axes 1) 1)
    _ ≤ S.long*dist (R.axes 0) (S.axes 0)+S.short*1 :=
      add_le_add
        (mul_le_mul (S.coordinate_difference_zero hx hy) (R.transverse_axis_le S)
          (abs_nonneg _) S.long_pos.le)
        (mul_le_mul (S.coordinate_difference_one hx hy) hc (abs_nonneg _) S.short_pos.le)
    _ = _ := by ring

theorem controlled_angle_containment (R S : Rectangle) (A : ℝ) (hA : 0≤A)
    (hL : S.long≤R.long) (hW : S.short≤R.short)
    (hangle : S.long*dist (R.axes 0) (S.axes 0)≤A*R.short)
    (hint : (R.carrier ∩ S.carrier).Nonempty) :
    S.carrier⊆(R.dilate (2*A+5) (by positivity)).carrier := by
  obtain ⟨z,hzR,hzS⟩ := hint
  intro x hx
  have he : R.axes.repr (x-R.center)=R.axes.repr (x-z)+R.axes.repr (z-R.center) := by
    rw [←map_add]
    congr 1
    abel
  constructor
  · change |R.axes.repr (x-R.center) 0|≤(2*A+5)*R.long/2
    rw [he,PiLp.add_apply]
    have ht := abs_add_le (R.axes.repr (x-z) 0) (R.axes.repr (z-R.center) 0)
    have hc := R.abs_coordinate_le_norm (x-z) 0
    have hd := S.dist_le_two_long hx hzS
    rw [dist_eq_norm] at hd
    nlinarith [hzR.1,R.long_pos]
  · change |R.axes.repr (x-R.center) 1|≤(2*A+5)*R.short/2
    rw [he,PiLp.add_apply]
    have ht := abs_add_le (R.axes.repr (x-z) 1) (R.axes.repr (z-R.center) 1)
    have hc := R.transverse_difference_le S hx hzS
    nlinarith [hzR.2,R.short_pos]

end LipschitzHilbert.Rectangle

end

end OAI
