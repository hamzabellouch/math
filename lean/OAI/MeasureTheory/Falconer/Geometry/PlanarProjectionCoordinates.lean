import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover

namespace OAI

/-! Coordinates supplied by two distinct planar projection directions.
These are the actual coordinates used by the dense scalar graph reduction. -/
namespace Falconer

noncomputable def planarProjectionCoordinates (a b : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (lineParameterProjection a l) (lineParameterProjection b l)

 theorem planar_projection_interpolation {a b y : ℝ} (hab : b ≠ a) (l : Space 2) :
    lineParameterProjection y l =
      ((b-y)/(b-a))*lineParameterProjection a l+
      ((y-a)/(b-a))*lineParameterProjection b l := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planar_projection_slope {a b : ℝ} (hab : b ≠ a) (l : Space 2) :
    l 0 = (lineParameterProjection b l-lineParameterProjection a l)/(b-a) := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planar_projection_intercept {a b : ℝ} (hab : b ≠ a) (l : Space 2) :
    l 1 = (b*lineParameterProjection a l-a*lineParameterProjection b l)/(b-a) := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planarProjectionCoordinates_injective {a b : ℝ} (hab : b ≠ a) :
    Function.Injective (planarProjectionCoordinates a b) := by
  intro l m he
  have h0 := congrArg (fun v : Space 2 => v 0) he
  have h1 := congrArg (fun v : Space 2 => v 1) he
  change lineParameterProjection a l = lineParameterProjection a m at h0
  change lineParameterProjection b l = lineParameterProjection b m at h1
  ext i
  fin_cases i
  · change l 0 = m 0
    rw [planar_projection_slope hab l,planar_projection_slope hab m,h0,h1]
  · change l 1 = m 1
    rw [planar_projection_intercept hab l,planar_projection_intercept hab m,h0,h1]

 theorem planar_projection_normalized {a b y : ℝ} (hab : b ≠ a) (hyb : y ≠ b) (l : Space 2) :
    lineParameterProjection a l+((y-a)/(b-y))*lineParameterProjection b l =
      ((b-a)/(b-y))*lineParameterProjection y l := by
  have hby : b-y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyb)
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planar_projection_ratio_bound {a b y r : ℝ} (hr : 0 < r)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hy : |y| ≤ 1)
    (hya : r ≤ |y-a|) (hby : r ≤ |b-y|) :
    (y-a)/(b-y) ≠ 0 ∧ |(y-a)/(b-y)| ≤ 2/r ∧ |((y-a)/(b-y))⁻¹| ≤ 2/r := by
  have hya0 : 0 < |y-a| := hr.trans_le hya
  have hby0 : 0 < |b-y| := hr.trans_le hby
  have hya' : y-a ≠ 0 := abs_pos.mp hya0
  have hby' : b-y ≠ 0 := abs_pos.mp hby0
  have hya2 : |y-a| ≤ 2 := (abs_sub y a).trans (by linarith)
  have hby2 : |b-y| ≤ 2 := (abs_sub b y).trans (by linarith)
  refine ⟨div_ne_zero hya' hby',?_,?_⟩
  · rw [abs_div]
    exact div_le_div₀ (by positivity) hya2 hr hby
  · rw [inv_div,abs_div]
    exact div_le_div₀ (by positivity) hby2 hr hya

 theorem planarProjectionCoordinates_dist_upper {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (l m : Space 2) : dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) ≤
      4*dist l m := by
  have h := planar_dist_le_coordinate_sum (planarProjectionCoordinates a b l)
    (planarProjectionCoordinates a b m)
  change dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) ≤
    |lineParameterProjection a l-lineParameterProjection a m|+
      |lineParameterProjection b l-lineParameterProjection b m| at h
  linarith [lineParameterProjection_dist ha l m,lineParameterProjection_dist hb l m]

 theorem planarProjectionCoordinates_dist_lower {a b : ℝ} (hab : b ≠ a)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (l m : Space 2) :
    dist l m ≤ (4/|b-a|)*dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) := by
  let u := lineParameterProjection a l-lineParameterProjection a m
  let v := lineParameterProjection b l-lineParameterProjection b m
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have h0 : |l 0-m 0| ≤ (|u|+|v|)/|b-a| := by
    rw [planar_projection_slope hab l,planar_projection_slope hab m,← sub_div,abs_div]
    apply div_le_div_of_nonneg_right _ hd.le
    have he : (lineParameterProjection b l-lineParameterProjection a l)-
        (lineParameterProjection b m-lineParameterProjection a m) = v-u := by dsimp [u,v]; ring
    rw [he]
    exact (abs_sub v u).trans_eq (by ring)
  have h1 : |l 1-m 1| ≤ (|u|+|v|)/|b-a| := by
    rw [planar_projection_intercept hab l,planar_projection_intercept hab m,← sub_div,abs_div]
    apply div_le_div_of_nonneg_right _ hd.le
    have he : (b*lineParameterProjection a l-a*lineParameterProjection b l)-
        (b*lineParameterProjection a m-a*lineParameterProjection b m) = b*u-a*v := by dsimp [u,v]; ring
    rw [he]
    have hh := abs_sub (b*u) (a*v)
    rw [abs_mul,abs_mul] at hh
    have hbu := mul_le_mul_of_nonneg_right hb (abs_nonneg u)
    have hav := mul_le_mul_of_nonneg_right ha (abs_nonneg v)
    nlinarith
  have hu : |u| ≤ dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) := by
    simpa only [planarProjectionCoordinates,rowPoint_zero,Real.dist_eq] using
      PiLp.dist_apply_le (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) 0
  have hv : |v| ≤ dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) := by
    simpa only [planarProjectionCoordinates,rowPoint_one,Real.dist_eq] using
      PiLp.dist_apply_le (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) 1
  have hh := planar_dist_le_coordinate_sum l m
  have h0' := (le_div_iff₀ hd).1 h0
  have h1' := (le_div_iff₀ hd).1 h1
  have hh' := mul_le_mul_of_nonneg_right hh hd.le
  have he : (4/|b-a|)*dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) =
      (4*dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m))/|b-a| := by ring
  rw [he]
  apply (le_div_iff₀ hd).2
  nlinarith

end Falconer

end OAI
