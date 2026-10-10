import OAI.Analysis.LipschitzHilbert.Estimates.SlopeOrthonormal
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleArea

namespace OAI

/-! An actual Euclidean rectangle enclosing a clipped thin slope
parallelogram, with the explicit lengths used in the popular-top proof. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

theorem slope_rectangle_short_le_long (s a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) :
    b/Real.sqrt (1+s^2) ≤
      Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b := by
  have hq : 1 ≤ Real.sqrt (1+s^2) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg s])
  have hqpos : 0 < Real.sqrt (1+s^2) := lt_of_lt_of_le zero_lt_one hq
  calc
    b/Real.sqrt (1+s^2) ≤ b := div_le_self hb.le hq
    _ ≤ a := hba
    _ ≤ Real.sqrt (1+s^2)*a := le_mul_of_one_le_left ha.le hq
    _ ≤ _ := le_add_of_nonneg_right (by positivity)

def slopeRectangle (c : ℝ × ℝ) (s a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) : Rectangle where
  center := planeCoordinates c
  axes := slopeAxes s
  long := Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b
  short := b/Real.sqrt (1+s^2)
  short_pos := div_pos hb (Real.sqrt_pos.mpr (by positivity))
  short_le_long := slope_rectangle_short_le_long s a b ha hb hba

theorem mem_slopeRectangle (c z : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hx : |z.1-c.1| ≤ a/2) (hy : |(z.2-c.2)-s*(z.1-c.1)| ≤ b/2) :
    planeCoordinates z ∈ (slopeRectangle c s a b ha hb hba).carrier := by
  have hqpos : 0 < Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have heq : ((z.1-c.1)+s*(z.2-c.2))/Real.sqrt (1+s^2) =
      Real.sqrt (1+s^2)*(z.1-c.1)+
        (s/Real.sqrt (1+s^2))*((z.2-c.2)-s*(z.1-c.1)) := by
    field_simp
    rw [hq2]
    ring
  change |(slopeAxes s).repr (planeCoordinates z-planeCoordinates c) 0| ≤ _ ∧
    |(slopeAxes s).repr (planeCoordinates z-planeCoordinates c) 1| ≤ _
  rw [slopeAxes_repr_zero, slopeAxes_repr_one]
  change |((z.1-c.1)+s*(z.2-c.2))/Real.sqrt (1+s^2)| ≤ _ ∧
    |((z.2-c.2)-s*(z.1-c.1))/Real.sqrt (1+s^2)| ≤ _
  constructor
  · rw [heq]
    calc
      _ ≤ |Real.sqrt (1+s^2)*(z.1-c.1)|+
          |(s/Real.sqrt (1+s^2))*((z.2-c.2)-s*(z.1-c.1))| := abs_add_le _ _
      _ = Real.sqrt (1+s^2)*|z.1-c.1|+
          (|s|/Real.sqrt (1+s^2))*|(z.2-c.2)-s*(z.1-c.1)| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hqpos]
      _ ≤ Real.sqrt (1+s^2)*(a/2)+(|s|/Real.sqrt (1+s^2))*(b/2) :=
        add_le_add (mul_le_mul_of_nonneg_left hx hqpos.le)
          (mul_le_mul_of_nonneg_left hy (by positivity))
      _ = _ := by dsimp [slopeRectangle]; ring
  · rw [abs_div, abs_of_pos hqpos]
    exact (div_le_div_of_nonneg_right hy hqpos.le).trans_eq (by dsimp [slopeRectangle]; ring)

theorem slope_rectangle_area_le (s a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (slopeRectangle (0,0) s a b ha hb hba).long *
      (slopeRectangle (0,0) s a b ha hb hba).short ≤ 2*a*b := by
  have hq : 0 < Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have heq : (Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b)*
      (b/Real.sqrt (1+s^2)) = a*b+(|s|/(1+s^2))*b^2 := by
    field_simp
    rw [hq2]
  change (Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b)*
    (b/Real.sqrt (1+s^2)) ≤ _
  rw [heq]
  have habs : |s| ≤ 1+s^2 := by
    nlinarith [sq_nonneg (|s|-(1/2:ℝ)), sq_abs s]
  have hratio : |s|/(1+s^2) ≤ 1 :=
    (div_le_one (by positivity : 0 < 1+s^2)).mpr habs
  have hm := mul_le_mul_of_nonneg_right hratio (sq_nonneg b)
  have hb2 := mul_le_mul_of_nonneg_right hba hb.le
  nlinarith

theorem slope_rectangle_long_le (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1) :
    (slopeRectangle c s a b ha hb hba).long ≤ 3*a := by
  have hq : 1 ≤ Real.sqrt (1+s^2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg s])
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have hu : Real.sqrt (1+s^2) ≤ 2 := by
    nlinarith [sq_abs s, abs_nonneg s]
  have hr : |s|/Real.sqrt (1+s^2) ≤ 1 :=
    (div_le_one (by linarith : 0 < Real.sqrt (1+s^2))).mpr (hs.trans hq)
  change Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b ≤ _
  have h1 := mul_le_mul_of_nonneg_right hu ha.le
  have h2 := mul_le_mul_of_nonneg_right hr hb.le
  nlinarith

theorem slope_rectangle_short_ge (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1) :
    b/2 ≤ (slopeRectangle c s a b ha hb hba).short := by
  have hqpos : 0 < Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have hq2 := Real.sq_sqrt (by positivity : 0 ≤ 1+s^2)
  have hu : Real.sqrt (1+s^2) ≤ 2 := by
    nlinarith [sq_abs s, abs_nonneg s]
  change b/2 ≤ b/Real.sqrt (1+s^2)
  apply (le_div_iff₀ hqpos).mpr
  nlinarith

theorem slope_rectangle_aperture_ge (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1) :
    b/(12*a) ≤ (slopeRectangle c s a b ha hb hba).short /
      (2*(slopeRectangle c s a b ha hb hba).long) := by
  let R := slopeRectangle c s a b ha hb hba
  have hlpos : 0 < R.long := R.short_pos.trans_le R.short_le_long
  have hlong : R.long ≤ 3*a := slope_rectangle_long_le c s a b ha hb hba hs
  have hshort : b/2 ≤ R.short := slope_rectangle_short_ge c s a b ha hb hba hs
  apply (div_le_div_iff₀ (by positivity : 0 < 12*a) (mul_pos (by norm_num) hlpos)).mpr
  have h1 := mul_le_mul_of_nonneg_left hlong hb.le
  have h2 := mul_le_mul_of_nonneg_left hshort ha.le
  nlinarith

theorem volume_slopeRectangle_le (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    volume (slopeRectangle c s a b ha hb hba).carrier ≤ ENNReal.ofReal (2*a*b) := by
  let R := slopeRectangle c s a b ha hb hba
  have hlong : 0 ≤ R.long := (R.short_pos.trans_le R.short_le_long).le
  rw [Rectangle.volume_carrier, ← ENNReal.ofReal_mul hlong]
  exact ENNReal.ofReal_le_ofReal (slope_rectangle_area_le s a b ha hb hba)

end LipschitzHilbert

end

end OAI
