import OAI.Geometry.CylinderCovering.Caps.FractionalDefinitions
import OAI.Geometry.CylinderCovering.Caps.CompensationEstimates
import OAI.Geometry.CylinderCovering.Radial.CapCoverage

namespace OAI

namespace CylinderCovering.HalfHeightCaps.FractionalEstimates
open CompensationEstimates

lemma P_half (r : ℝ) : P (r / 2) = alpha r := by
  unfold P alpha
  ring

lemma g_half (r : ℝ) : g (r / 2) = F r := by
  unfold g P F
  ring

lemma defect (X Y : ℝ) :
    g X + g Y - P X * Y ^ 2 - P Y * X ^ 2 = (X ^ 2 - Y ^ 2) ^ 2 := by
  unfold g P
  ring

lemma square_difference {δ y r : ℝ} (hδ : 0 ≤ δ)
    (hy : |y| ≤ 1) (hr : |r| ≤ 1) (he : |y-r/2| ≤ 3*δ/2) :
    |y^2-r^2/4| ≤ 9*δ/4 := by
  have hsum : |y+r/2| ≤ 3/2 := by
    calc
      |y+r/2| ≤ |y|+|r/2| := abs_add_le _ _
      _ ≤ 3/2 := by rw [abs_div]; norm_num; linarith
  have hp : |(y-r/2)*(y+r/2)| ≤ (3*δ/2)*(3/2) := by
    rw [abs_mul]
    exact mul_le_mul he hsum (abs_nonneg _) (by positivity)
  have hid : (y-r/2)*(y+r/2) = y^2-r^2/4 := by ring
  rw [hid] at hp
  convert hp using 1
  ring

lemma polynomial_errors {δ y r : ℝ} (hδ : 0 ≤ δ)
    (hy : |y| ≤ 1) (hr : |r| ≤ 1) (he : |y-r/2| ≤ 3*δ/2) :
    |P y-alpha r| ≤ 9*δ/4 ∧ |g y-F r| ≤ 27*δ/8 := by
  have hd := square_difference hδ hy hr he
  have idP : P y-alpha r = y^2-r^2/4 := by unfold P alpha; ring
  have idg : g y-F r = (y^2-r^2/4)*(1/4+y^2+r^2/4) := by
    unfold g P F
    ring
  have hfactor0 : 0 ≤ 1/4+y^2+r^2/4 := by positivity
  have hfactor : 1/4+y^2+r^2/4 ≤ 3/2 := by
    nlinarith only [square_le_one hy, square_le_one hr]
  refine ⟨by rwa [idP], ?_⟩
  rw [idg, abs_mul, abs_of_nonneg hfactor0]
  calc
    |y^2-r^2/4| *(1/4+y^2+r^2/4) ≤ (9*δ/4)*(3/2) :=
      mul_le_mul hd hfactor hfactor0 (by positivity)
    _ = 27*δ/8 := by ring

lemma profile_comparison {δ x y r : ℝ} (hδ : 0 ≤ δ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hr : |r| ≤ 1)
    (he : |y-r/2| ≤ 3*δ/2) :
    g y-P y*x^2 ≤ F r-alpha r*x^2+45*δ/8 := by
  obtain ⟨hP,hg⟩ := polynomial_errors hδ hy hr he
  have hx2 := square_le_one hx
  have hPlo := (abs_le.mp hP).1
  have hgup := (abs_le.mp hg).2
  have hp := mul_le_mul_of_nonneg_right hPlo (sq_nonneg x)
  have hbound := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ 9*δ/4 by positivity)
  nlinarith only [hp,hbound,hgup]

lemma first_identity {δ x y z r u : ℝ}
    (hy : y=u*r+δ*x*alpha r) (hz : z=u+δ*x*beta r) :
    z=1/2+δ*x*y-δ^2*alpha r*x^2+(u-1/2)*(1-δ*r*x) := by
  unfold alpha beta at *
  linear_combination hz - δ*x*hy

lemma fractional_le_square {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/2) :
    0 ≤ δ^(5/2:ℝ) ∧ δ^(5/2:ℝ) ≤ δ^2 := by
  rw [RadialCapCoverage.fractional_power δ hδ]
  have hs : Real.sqrt δ ≤ 1 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> linarith
  exact ⟨by positivity, by nlinarith only [mul_le_mul_of_nonneg_left hs (sq_nonneg δ)]⟩

theorem first_failure_estimate {δ x y z r u : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1/2)
    (hx : |x| ≤ 1) (hyb : |y| ≤ 1) (hr : |r| ≤ 1)
    (he : |y-r/2| ≤ 3*δ/2)
    (hy : y=u*r+δ*x*alpha r) (hz : z=u+δ*x*beta r)
    (hfail : fractionalCap δ r < u) :
    1/2+δ*x*y+δ^2*(g y-P y*x^2)+δ^(5/2:ℝ)-7*δ^3 < z := by
  have hf0 := (profile_bounds hr).1
  have hf1 := (profile_bounds hr).2
  obtain ⟨hp0,hp1⟩ := fractional_le_square hδ hsmall
  have hw := (weight_bounds hδ.le hsmall hx hr).2.2.1
  have hwp : 0 < 1-δ*r*x := by nlinarith only [hw]
  have hfail' : δ^2*F r+δ^(5/2:ℝ) < u-1/2 := by
    unfold fractionalCap at hfail
    linarith
  have hstrict := mul_lt_mul_of_pos_right hfail' hwp
  have hprof := mul_le_mul_of_nonneg_left
    (profile_comparison hδ.le hx hyb hr he) (sq_nonneg δ)
  have hprod := (abs_le.mp (abs_product_le_one hx hr)).2
  have htotal0 : 0 ≤ δ^2*F r+δ^(5/2:ℝ) := by positivity
  have htotal1 : δ^2*F r+δ^(5/2:ℝ) ≤ 9*δ^2/8 := by
    have := mul_le_mul_of_nonneg_left hf1 (sq_nonneg δ)
    nlinarith only [this,hp1]
  have hweight := mul_le_mul_of_nonneg_left hprod hδ.le
  have hloss1 := mul_le_mul_of_nonneg_right hweight htotal0
  have hloss2 := mul_le_mul_of_nonneg_left htotal1 hδ.le
  have hid := first_identity hy hz
  have hcube : 0 < δ^3 := pow_pos hδ 3
  nlinarith only [hstrict,hprof,hloss1,hloss2,hid,hcube]

theorem paired_failure_estimates {δ X Y Z r s u v : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1/2)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hY : Y=u*r+δ*X*alpha r) (hZ : Z=u+δ*X*beta r)
    (hX : X=v*s-δ*Y*alpha s) (hZv : 1-Z=v-δ*Y*beta s)
    (hu : fractionalCap δ r < u) (hv : fractionalCap δ s < v) :
    (1/2+δ*X*Y+δ^2*(g Y-P Y*X^2)+δ^(5/2:ℝ)-7*δ^3 < Z) ∧
    (Z < 1/2+δ*X*Y-δ^2*(g X-P X*Y^2)-δ^(5/2:ℝ)+7*δ^3) := by
  have hp0 : 0 ≤ δ^(5/2:ℝ) := Real.rpow_nonneg hδ.le _
  have hur : 1/2 ≤ u := by
    have hf := mul_nonneg (sq_nonneg δ) (profile_bounds hr).1
    unfold fractionalCap at hu
    linarith
  have hvs : 1/2 ≤ v := by
    have hf := mul_nonneg (sq_nonneg δ) (profile_bounds hs).1
    unfold fractionalCap at hv
    linarith
  obtain ⟨hYr,hXs⟩ := angular_errors hδ.le hsmall hXb hYb hr hs
    hur hvs hY hZ hX hZv
  refine ⟨first_failure_estimate hδ hsmall hXb hYb hr hYr hY hZ hu, ?_⟩
  have heqX : X=v*s+δ*(-Y)*alpha s := by nlinarith only [hX]
  have heqZ : 1-Z=v+δ*(-Y)*beta s := by nlinarith only [hZv]
  have hsecond := first_failure_estimate hδ hsmall
    (x := -Y) (by simpa only [abs_neg] using hYb) hXb hs hXs heqX heqZ hv
  nlinarith only [hsecond]

lemma fractional_dominates_cube {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/64) :
    8*δ^3 ≤ δ^(5/2:ℝ) := by
  have hs0 := Real.sqrt_nonneg δ
  have hs2 := Real.sq_sqrt hδ.le
  have hs : Real.sqrt δ ≤ 1/8 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith only [hsmall]
  have hprod := mul_le_mul_of_nonneg_left hs hs0
  have hlinear : 8*δ ≤ Real.sqrt δ := by nlinarith only [hprod,hs2]
  have hfinal := mul_le_mul_of_nonneg_left hlinear (sq_nonneg δ)
  rw [RadialCapCoverage.fractional_power δ hδ]
  nlinarith only [hfinal]

theorem fractional_failures_incompatible {δ X Y Z r s u v : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1/64)
    (hXb : |X| ≤ 1) (hYb : |Y| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (hY : Y=u*r+δ*X*alpha r) (hZ : Z=u+δ*X*beta r)
    (hX : X=v*s-δ*Y*alpha s) (hZv : 1-Z=v-δ*Y*beta s) :
    ¬ (fractionalCap δ r < u ∧ fractionalCap δ s < v) := by
  rintro ⟨hu,hv⟩
  obtain ⟨hlo,hhi⟩ := paired_failure_estimates hδ (by linarith) hXb hYb hr hs
    hY hZ hX hZv hu hv
  have hd : 0 ≤ g X+g Y-P X*Y^2-P Y*X^2 := by
    rw [defect]
    positivity
  have hscaled := mul_nonneg (sq_nonneg δ) hd
  have hfrac := fractional_dominates_cube hδ hsmall
  have hcube : 0 < δ^3 := pow_pos hδ 3
  nlinarith only [hlo,hhi,hscaled,hfrac,hcube]

end CylinderCovering.HalfHeightCaps.FractionalEstimates

end OAI
