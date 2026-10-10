import OAI.Geometry.CylinderCovering.Caps.CapsDefinitions

namespace OAI

namespace CylinderCovering.HalfHeightCaps.CompensationEstimates

lemma square_le_one {x : ℝ} (hx : |x| ≤ 1) : x^2 ≤ 1 := by
  nlinarith only [sq_abs x, abs_nonneg x, hx]

lemma alpha_bounds {r : ℝ} (hr : |r| ≤ 1) : 0 ≤ alpha r ∧ alpha r ≤ 1/2 := by
  have h := square_le_one hr
  unfold alpha
  constructor
  · positivity
  · linarith

lemma profile_bounds {r : ℝ} (hr : |r| ≤ 1) : 0 ≤ F r ∧ F r ≤ 1/8 := by
  have h := square_le_one hr
  have hprod := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr h)
  unfold F
  constructor
  · positivity
  · nlinarith only [h, sq_nonneg r, hprod]

lemma abs_product_le_one {x r : ℝ} (hx : |x| ≤ 1) (hr : |r| ≤ 1) :
    |x*r| ≤ 1 := by
  rw [abs_mul]
  nlinarith only [hx, hr, abs_nonneg x, abs_nonneg r,
    mul_nonneg (sub_nonneg.mpr hx) (abs_nonneg r)]

lemma weight_bounds {δ x r : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hx : |x| ≤ 1) (hr : |r| ≤ 1) :
    1-δ ≤ 1-δ*x*r ∧ 1-δ ≤ 1+δ*x*r ∧
    1/2 ≤ 1-δ*x*r ∧ 1/2 ≤ 1+δ*x*r := by
  have hp := abs_product_le_one hx hr
  have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hp).1 hδ
  have hhigh := mul_le_mul_of_nonneg_left (abs_le.mp hp).2 hδ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith only [hlow,hhigh,hδsmall]

lemma weighted_square_le_half {x r : ℝ} (hx : |x| ≤ 1) (hr : |r| ≤ 1) :
    x^2 * alpha r ≤ 1/2 := by
  have hs := square_le_one hx
  obtain ⟨ha,ha'⟩ := alpha_bounds hr
  have hm := mul_le_mul_of_nonneg_right hs ha
  nlinarith only [hm,ha']

lemma identity {δ X Y Z r s u v : ℝ}
    (hY : Y = u*r+δ*X*alpha r) (hZ : Z = u+δ*X*beta r)
    (hX : X = v*s-δ*Y*alpha s) (hZv : 1-Z = v-δ*Y*beta s) :
    (u-1/2)*(1-δ*X*r)+(v-1/2)*(1+δ*Y*s) =
      δ^2*(X^2*alpha r+Y^2*alpha s) := by
  unfold alpha beta at *
  linear_combination δ*X*hY-δ*Y*hX-hZ-hZv

theorem radial_excess_bounds {δ X Y Z r s u v : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hu : 1/2 ≤ u) (hv : 1/2 ≤ v)
    (hY : Y = u*r+δ*X*alpha r) (hZ : Z = u+δ*X*beta r)
    (hX : X = v*s-δ*Y*alpha s) (hZv : 1-Z = v-δ*Y*beta s) :
    0 ≤ u-1/2 ∧ u-1/2 ≤ 2*δ^2 ∧ 0 ≤ v-1/2 ∧ v-1/2 ≤ 2*δ^2 := by
  have hcomp := identity hY hZ hX hZv
  have hwU := (weight_bounds hδ hδsmall hXb hr).2.2.1
  have hwV := (weight_bounds hδ hδsmall hYb hs).2.2.2
  have hA : X^2*alpha r+Y^2*alpha s ≤ 1 := by
    linarith only [weighted_square_le_half hXb hr, weighted_square_le_half hYb hs]
  have hsum := mul_le_mul_of_nonneg_left hA (sq_nonneg δ)
  have hu0 : 0 ≤ u-1/2 := by linarith
  have hv0 : 0 ≤ v-1/2 := by linarith
  have hU := mul_le_mul_of_nonneg_left hwU hu0
  have hV := mul_le_mul_of_nonneg_left hwV hv0
  exact ⟨hu0, by nlinarith only [hcomp,hsum,hU,hV,hv0],
    hv0, by nlinarith only [hcomp,hsum,hU,hV,hu0]⟩

lemma radial_coordinate_error {δ x r u y : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hx : |x| ≤ 1) (hr : |r| ≤ 1)
    (hu0 : 0 ≤ u-1/2) (hu : u-1/2 ≤ 2*δ^2)
    (hy : y = u*r+δ*x*alpha r) : |y-r/2| ≤ 3*δ/2 := by
  obtain ⟨ha,ha'⟩ := alpha_bounds hr
  have heq : y-r/2 = (u-1/2)*r+δ*x*alpha r := by rw [hy]; ring
  have hfirst : |(u-1/2)*r| ≤ 2*δ^2 := by
    rw [abs_mul,abs_of_nonneg hu0]
    calc
      (u-1/2)*|r| ≤ (u-1/2)*1 := mul_le_mul_of_nonneg_left hr hu0
      _ ≤ 2*δ^2 := by simpa using hu
  have hsecond : |δ*x*alpha r| ≤ δ/2 := by
    rw [abs_mul,abs_mul,abs_of_nonneg hδ,abs_of_nonneg ha]
    calc
      δ * |x| * alpha r ≤ δ*1*(1/2) := by gcongr
      _ = δ/2 := by ring
  rw [heq]
  have htriangle := abs_add_le ((u-1/2)*r) (δ*x*alpha r)
  have hquad := mul_le_mul_of_nonneg_left hδsmall hδ
  nlinarith only [htriangle,hfirst,hsecond,hquad]

theorem angular_errors {δ X Y Z r s u v : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hu : 1/2 ≤ u) (hv : 1/2 ≤ v)
    (hY : Y = u*r+δ*X*alpha r) (hZ : Z = u+δ*X*beta r)
    (hX : X = v*s-δ*Y*alpha s) (hZv : 1-Z = v-δ*Y*beta s) :
    |Y-r/2| ≤ 3*δ/2 ∧ |X-s/2| ≤ 3*δ/2 := by
  obtain ⟨hu0,hu',hv0,hv'⟩ := radial_excess_bounds hδ hδsmall hXb hYb hr hs hu hv hY hZ hX hZv
  refine ⟨radial_coordinate_error hδ hδsmall hXb hr hu0 hu' hY, ?_⟩
  apply radial_coordinate_error hδ hδsmall (x := -Y) (by simpa using hYb) hs hv0 hv'
  nlinarith only [hX]

lemma squared_error {δ x s : ℝ} (hδ : 0 ≤ δ) (hx : |x| ≤ 1) (hs : |s| ≤ 1)
    (he : |x-s/2| ≤ 3*δ/2) : x^2 ≤ s^2/4+9*δ/4 := by
  have hsum : |x+s/2| ≤ 3/2 := by
    calc
      |x+s/2| ≤ |x|+|s/2| := abs_add_le _ _
      _ ≤ 1+1/2 := by rw [abs_div]; norm_num; linarith
      _ = 3/2 := by norm_num
  have hprod : |(x-s/2)*(x+s/2)| ≤ (3*δ/2)*(3/2) := by
    rw [abs_mul]
    exact mul_le_mul he hsum (abs_nonneg _) (by positivity)
  have hid : (x-s/2)*(x+s/2)=x^2-s^2/4 := by ring
  rw [hid] at hprod
  nlinarith only [(abs_le.mp hprod).2]

lemma monotone_profile_comparison (r s : ℝ) :
    (s^2*alpha r+r^2*alpha s)/4 ≤ F r+F s := by
  unfold alpha F
  nlinarith only [sq_nonneg (r^2-s^2)]

theorem weighted_comparison {δ X Y r s : ℝ} (hδ : 0 ≤ δ)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hYr : |Y-r/2| ≤ 3*δ/2) (hXs : |X-s/2| ≤ 3*δ/2) :
    X^2*alpha r+Y^2*alpha s ≤ (s^2*alpha r+r^2*alpha s)/4+9*δ/4 ∧
    X^2*alpha r+Y^2*alpha s ≤ F r+F s+9*δ/4 := by
  obtain ⟨har,har'⟩ := alpha_bounds hr
  obtain ⟨has,has'⟩ := alpha_bounds hs
  have hx := mul_le_mul_of_nonneg_right (squared_error hδ hXb hs hXs) har
  have hy := mul_le_mul_of_nonneg_right (squared_error hδ hYb hr hYr) has
  have hsum := mul_le_mul_of_nonneg_left (add_le_add har' has') hδ
  have hfirst : X^2*alpha r+Y^2*alpha s ≤
      (s^2*alpha r+r^2*alpha s)/4+9*δ/4 := by nlinarith only [hx,hy,hsum]
  exact ⟨hfirst, hfirst.trans (by linarith only [monotone_profile_comparison r s])⟩

theorem cubic_padding_lower {δ r s : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) :
    F r+F s+15*δ/4 ≤ (1-δ)*(F r+F s+8*δ) := by
  have hrF := (profile_bounds hr).2
  have hsF := (profile_bounds hs).2
  have hcoef : 0 ≤ 17/4-8*δ-(F r+F s) := by linarith
  have hprod := mul_nonneg hδ hcoef
  nlinarith only [hprod]

theorem cubic_failure_lower {δ X Y r s u v : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/2)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hu : cubicCap δ r < u) (hv : cubicCap δ s < v) :
    δ^2*(F r+F s+15*δ/4) <
      (u-1/2)*(1-δ*X*r)+(v-1/2)*(1+δ*Y*s) := by
  have hδone : 0 < 1-δ := by linarith
  have hFr := (profile_bounds hr).1
  have hFs := (profile_bounds hs).1
  have hu' : δ^2*F r+4*δ^3 < u-1/2 := by unfold cubicCap at hu; linarith
  have hv' : δ^2*F s+4*δ^3 < v-1/2 := by unfold cubicCap at hv; linarith
  have hcapr : 0 ≤ δ^2*F r+4*δ^3 := by positivity
  have hu0 : 0 ≤ u-1/2 := hcapr.trans hu'.le
  have hcaps : 0 ≤ δ^2*F s+4*δ^3 := by positivity
  have hv0 : 0 ≤ v-1/2 := hcaps.trans hv'.le
  have hUstrict := mul_lt_mul_of_pos_right hu' hδone
  have hVstrict := mul_lt_mul_of_pos_right hv' hδone
  have hUweak := mul_le_mul_of_nonneg_left (weight_bounds hδ.le hδsmall hXb hr).1 hu0
  have hVweak := mul_le_mul_of_nonneg_left (weight_bounds hδ.le hδsmall hYb hs).2.1 hv0
  have hpad := mul_le_mul_of_nonneg_left (cubic_padding_lower hδ.le hδsmall hr hs)
    (sq_nonneg δ)
  nlinarith only [hUstrict,hVstrict,hUweak,hVweak,hpad]

theorem cubic_failures_incompatible {δ X Y Z r s u v : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/2)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hY : Y = u*r+δ*X*alpha r) (hZ : Z = u+δ*X*beta r)
    (hX : X = v*s-δ*Y*alpha s) (hZv : 1-Z = v-δ*Y*beta s) :
    ¬ (cubicCap δ r < u ∧ cubicCap δ s < v) := by
  rintro ⟨hu,hv⟩
  have hFr := (profile_bounds hr).1
  have hFs := (profile_bounds hs).1
  have huc : 1/2 ≤ cubicCap δ r := by
    have hnonneg : 0 ≤ δ^2*F r+4*δ^3 := by positivity
    unfold cubicCap
    linarith
  have hvc : 1/2 ≤ cubicCap δ s := by
    have hnonneg : 0 ≤ δ^2*F s+4*δ^3 := by positivity
    unfold cubicCap
    linarith
  obtain ⟨hYr,hXs⟩ := angular_errors hδ.le hδsmall hXb hYb hr hs
    (huc.trans hu.le) (hvc.trans hv.le) hY hZ hX hZv
  have hupper := (weighted_comparison hδ.le hXb hYb hr hs hYr hXs).2
  have hlower := cubic_failure_lower hδ hδsmall hXb hYb hr hs hu hv
  rw [identity hY hZ hX hZv] at hlower
  have hupper' := mul_le_mul_of_nonneg_left hupper (sq_nonneg δ)
  have hcube : 0 < δ^3 := pow_pos hδ 3
  nlinarith only [hlower,hupper',hcube]

end CylinderCovering.HalfHeightCaps.CompensationEstimates

end OAI
