import OAI.Analysis.LipschitzHilbert.Geometry.RectangleArea
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! Elementary geometry for the finite rectangle covering proof of
Lacey--Li, Memoirs AMS 205 (2010), Chapter 3. All rectangles and popularity
sets here are the actual objects from the published input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert.Rectangle

theorem long_pos (R : Rectangle) : 0<R.long := R.short_pos.trans_le R.short_le_long

theorem aperture_pos (R : Rectangle) : 0<R.short/(2*R.long) := by
  exact div_pos R.short_pos (mul_pos (by norm_num) R.long_pos)

theorem aperture_le_half (R : Rectangle) : R.short/(2*R.long) ≤ 1/2 := by
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) R.long_pos)).mpr
  linarith [R.short_le_long]

theorem norm_sub_center_le_long (R : Rectangle) {x : Plane} (hx : x∈R.carrier) :
    ‖x-R.center‖ ≤ R.long := by
  have h0 := hx.1
  have h1 := hx.2
  calc
    ‖x-R.center‖ = ‖∑ i : Fin 2, R.axes.repr (x-R.center) i • R.axes i‖ := by
      rw [R.axes.sum_repr]
    _  ≤  ∑ i : Fin 2, ‖R.axes.repr (x-R.center) i • R.axes i‖ := norm_sum_le _ _
    _ = |R.axes.repr (x-R.center) 0|+|R.axes.repr (x-R.center) 1| := by
      simp only [Fin.sum_univ_two,norm_smul,R.axes.norm_eq_one,mul_one,Real.norm_eq_abs]
    _  ≤  R.long := by linarith [R.short_le_long]

theorem dist_le_two_long (R : Rectangle) {x y : Plane} (hx : x∈R.carrier) (hy : y∈R.carrier) :
    dist x y ≤ 2*R.long := by
  have ht := dist_triangle x R.center y
  rw [dist_comm R.center y,dist_eq_norm x R.center,dist_eq_norm y R.center] at ht
  linarith [R.norm_sub_center_le_long hx,R.norm_sub_center_le_long hy]

theorem measurableSet_popularSet (R : Rectangle) {v : Plane → Plane} (hv : Continuous v) :
    MeasurableSet (R.popularSet v) := by
  change MeasurableSet (R.carrier ∩ {x | Real.cos (R.short/(2*R.long)) ≤ inner ℝ (v x) (R.axes 0)})
  apply R.measurableSet_carrier.inter
  have hi : Continuous (fun x => inner ℝ (v x) (R.axes 0)) := hv.inner continuous_const
  exact (isClosed_le continuous_const hi).measurableSet

theorem popular_axis_distance (R : Rectangle) {v : Plane → Plane}
    (hu : ∀ x, ‖v x‖=1) {x : Plane} (hx : x∈R.popularSet v) :
    dist (v x) (R.axes 0) ≤ R.short/(2*R.long) := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=R.short/(2*R.long))
  have hinner := hx.2
  have he := norm_sub_sq_real (v x) (R.axes 0)
  rw [hu x,R.axes.norm_eq_one] at he
  rw [dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) R.aperture_pos.le).mp
  nlinarith

theorem popularSet_nonempty (R : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hR : R.Admissible v K δ) (hδ : 0<δ) : (R.popularSet v).Nonempty := by
  have hpos : 0<(δ:ℝ≥0∞)*volume R.carrier :=
    ENNReal.mul_pos (by exact_mod_cast hδ.ne') R.volume_carrier_pos.ne'
  have hne : volume (R.popularSet v)≠0 := ne_of_gt (hpos.trans_le hR.2)
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty.mp h,measure_empty] at hne
  contradiction

theorem popular_points_distance (R S : Rectangle) {v : Plane → Plane}
    {x y z : Plane} (hx : x∈R.popularSet v) (hy : y∈S.popularSet v)
    (hzR : z∈R.carrier) (hzS : z∈S.carrier) : dist x y ≤ 2*(R.long+S.long) := by
  have ht := dist_triangle x z y
  have hR := R.dist_le_two_long hx.1 hzR
  have hS := S.dist_le_two_long hzS hy.1
  linarith

theorem intersecting_axes_distance (R S : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖=1) (hδ : 0<δ)
    (hR : R.Admissible v K δ) (hS : S.Admissible v K δ)
    (hint : (R.carrier ∩ S.carrier).Nonempty) :
    dist (R.axes 0) (S.axes 0) ≤ R.short/(2*R.long)+S.short/(2*S.long)+
      2*(K:ℝ)*(R.long+S.long) := by
  obtain ⟨x,hx⟩ := R.popularSet_nonempty hR hδ
  obtain ⟨y,hy⟩ := S.popularSet_nonempty hS hδ
  obtain ⟨z,hzR,hzS⟩ := hint
  have hxy := hv.dist_le_mul x y
  have hxy' := R.popular_points_distance S hx hy hzR hzS
  have hm := mul_le_mul_of_nonneg_left hxy' K.coe_nonneg
  have ht1 := dist_triangle (R.axes 0) (v x) (S.axes 0)
  have ht2 := dist_triangle (v x) (v y) (S.axes 0)
  have hRx := R.popular_axis_distance hu hx
  have hSy := S.popular_axis_distance hu hy
  rw [dist_comm (R.axes 0) (v x)] at ht1
  linarith

end LipschitzHilbert.Rectangle

end

end OAI
