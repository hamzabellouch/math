import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ModelFiniteTests

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain LoewnerRestart FlowIdentification

lemma lineMap_im_lower {z w : ℂ} {y : ℝ} (hz : y≤z.im) (hw : y≤w.im)
    {t : ℝ} (ht : t∈Icc 0 1) : y≤(AffineMap.lineMap z w t).im := by
  rw [AffineMap.lineMap_apply]
  simp only [vadd_eq_add,vsub_eq_sub,Complex.sub_im,Complex.add_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hz),
    mul_nonneg ht.1 (sub_nonneg.mpr hw)]

lemma lineMap_hasDerivAt_complex_comp {f : ℂ→ℂ} {f' z w : ℂ} {t : ℝ}
    (hd : HasDerivAt f f' (AffineMap.lineMap z w t)) :
    HasDerivAt (fun t : ℝ=>f (AffineMap.lineMap z w t)) (f'*(w-z)) t := by
  have hh := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ) (a := z) (b := w) (x := t))
  convert! hh using 1
  change f'*(w-z)=(w-z)*f'
  ring

 
lemma norm_exp_bound_on_halfPlane_segment {f : ℂ→ℂ} {M y : ℝ}
    (hy : 0<y) (hM : 0≤M)
    (hd : ∀v : ℂ,0<v.im → DifferentiableAt ℂ f v)
    (hb : ∀v : ℂ,0<v.im → ‖deriv f v‖≤(M/v.im)*‖f v‖)
    {z w : ℂ} (hz : y≤z.im) (hw : y≤w.im) :
    ‖f w‖≤‖f z‖*Real.exp ((M/y)*‖w-z‖) := by
  let K : ℝ := (M/y)*‖w-z‖
  let g : ℝ→ℂ := fun t=>f (AffineMap.lineMap z w t)
  let dg : ℝ→ℂ := fun t=>deriv f (AffineMap.lineMap z w t)*(w-z)
  have hi (t : ℝ) (ht : t∈Icc 0 1) : 0<(AffineMap.lineMap z w t).im :=
    hy.trans_le (lineMap_im_lower hz hw ht)
  have hg (t : ℝ) (ht : t∈Icc 0 1) : HasDerivAt g (dg t) t :=
    lineMap_hasDerivAt_complex_comp (hd _ (hi t ht)).hasDerivAt
  have hc : ContinuousOn g (Icc 0 1) := fun t ht=>(hg t ht).continuousAt.continuousWithinAt
  have hdb (t : ℝ) (ht : t∈Ico 0 1) : ‖dg t‖≤K*‖g t‖+0 := by
    dsimp only [dg,g,K]
    rw [norm_mul,add_zero]
    calc
      _ ≤ ((M/(AffineMap.lineMap z w t).im)*‖f (AffineMap.lineMap z w t)‖)*‖w-z‖ :=
        mul_le_mul_of_nonneg_right (hb _ (hi t (Ico_subset_Icc_self ht))) (norm_nonneg _)
      _ ≤ ((M/y)*‖f (AffineMap.lineMap z w t)‖)*‖w-z‖ := by
        gcongr
        exact lineMap_im_lower hz hw (Ico_subset_Icc_self ht)
      _ = _ := by ring
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hc
    (fun t ht=>(hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (le_rfl : ‖g 0‖≤‖g 0‖) hdb 1 (by norm_num : (1:ℝ)∈Icc 0 1)
  simpa only [g,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,sub_zero,
    gronwallBound_ε0,mul_one] using hh

 
theorem inverseMap_deriv_segment_bound {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z w : ℂ} {y : ℝ} (hy : 0<y) (hz : y≤z.im) (hw : y≤w.im) :
    ‖deriv (inverseMap a b T) w‖ ≤ ‖deriv (inverseMap a b T) z‖*
      Real.exp ((3/y)*‖w-z‖) :=
  norm_exp_bound_on_halfPlane_segment hy (by norm_num)
    (fun v hv=>(hasDerivAt_deriv_inverseMap ha b T hv).differentiableAt)
    (fun v hv=>inverseMap_preSchwarzian_bound ha b T hv) hz hw

 

theorem inverseMap_deriv_two_sided {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z w : ℂ} {y L : ℝ} (hy : 0<y) (hz : y≤z.im) (hw : y≤w.im)
    (hd : ‖w-z‖≤L) :
    ‖deriv (inverseMap a b T) z‖*Real.exp (-(3/y)*L)≤‖deriv (inverseMap a b T) w‖ ∧
    ‖deriv (inverseMap a b T) w‖≤‖deriv (inverseMap a b T) z‖*Real.exp ((3/y)*L) := by
  have hK : 0≤3/y := by positivity
  have up := (inverseMap_deriv_segment_bound ha b T hy hz hw).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hK)) (norm_nonneg _))
  have rev := (inverseMap_deriv_segment_bound ha b T hy hw hz).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hd) hK)) (norm_nonneg _))
  refine ⟨?_,up⟩
  have hh := mul_le_mul_of_nonneg_right rev (Real.exp_pos (-(3/y)*L)).le
  rwa [mul_assoc,←Real.exp_add,show (3/y)*L+(-(3/y)*L)=0 by ring,Real.exp_zero,mul_one] at hh

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain LoewnerRestart FlowIdentification

lemma im_lower_of_mem_closedBall {w z : ℂ} {r : ℝ} (hw : w∈closedBall z r) :
    z.im-r≤w.im := by
  have hh := (Complex.im_le_norm (z-w)).trans (by
    simpa only [norm_sub_rev,←dist_eq_norm] using mem_closedBall.mp hw)
  rw [Complex.sub_im] at hh
  linarith

lemma smallBall_im_half {z w : ℂ} (hz : 0<z.im) (hw : w∈closedBall z (z.im/100)) :
    z.im/2≤w.im := by
  have := im_lower_of_mem_closedBall hw
  linarith

lemma inverseMap_deriv_smallBall_bound {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z w : ℂ} (hz : 0<z.im) (hw : w∈closedBall z (z.im/100)) :
    ‖deriv (inverseMap a b T) w‖≤3*‖deriv (inverseMap a b T) z‖ := by
  have h := inverseMap_deriv_segment_bound ha b T (by positivity : 0<z.im/2)
    (by linarith : z.im/2≤z.im) (smallBall_im_half hz hw)
  have hk : (3/(z.im/2))*‖w-z‖≤1 := by
    have hh : ‖w-z‖≤z.im/100 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    apply le_trans (mul_le_mul_of_nonneg_left hh (by positivity))
    field_simp
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_left
    ((Real.exp_le_exp.mpr hk).trans Real.exp_one_lt_three.le) (norm_nonneg _)).trans_eq (mul_comm _ _))

lemma inverseMap_second_deriv_smallBall_bound {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z w : ℂ} (hz : 0<z.im) (hw : w∈closedBall z (z.im/100)) :
    ‖deriv (deriv (inverseMap a b T)) w‖≤(18/z.im)*‖deriv (inverseMap a b T) z‖ := by
  have hi := smallBall_im_half hz hw
  have hw0 : 0<w.im := lt_of_lt_of_le (by positivity : 0<z.im/2) hi
  apply (inverseMap_preSchwarzian_bound ha b T hw0).trans
  calc
    _ ≤ (3/(z.im/2))*(3*‖deriv (inverseMap a b T) z‖) := by
      gcongr
      exact inverseMap_deriv_smallBall_bound ha b T hz hw
    _ = _ := by ring

lemma inverseMap_deriv_close_on_smallBall {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z w : ℂ} (hz : 0<z.im) (hw : w∈closedBall z (z.im/100)) :
    ‖deriv (inverseMap a b T) w-deriv (inverseMap a b T) z‖≤‖deriv (inverseMap a b T) z‖/2 := by
  have hd (v : ℂ) (hv : v∈closedBall z (z.im/100)) :
      HasFDerivWithinAt (deriv (inverseMap a b T))
        (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv (inverseMap a b T)) v))
        (closedBall z (z.im/100)) v := by
    have hh := hasDerivAt_deriv_inverseMap ha b T
      (lt_of_lt_of_le (by positivity : 0<z.im/2) (smallBall_im_half hz hv))
    rw [←hh.deriv] at hh
    exact hh.hasFDerivAt.hasFDerivWithinAt
  have hh := (convex_closedBall z (z.im/100)).norm_image_sub_le_of_norm_hasFDerivWithin_le hd
    (fun v hv=>by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using
      inverseMap_second_deriv_smallBall_bound ha b T hz hv)
    (mem_closedBall_self (by positivity)) hw
  have hn : ‖w-z‖≤z.im/100 := by simpa only [mem_closedBall,dist_eq_norm] using hw
  apply hh.trans
  calc
    _ ≤ ((18/z.im)*‖deriv (inverseMap a b T) z‖)*(z.im/100) := by gcongr
    _ = (18/100:ℝ)*‖deriv (inverseMap a b T) z‖ := by field_simp
    _ ≤ ‖deriv (inverseMap a b T) z‖/2 := by nlinarith [norm_nonneg (deriv (inverseMap a b T) z)]

lemma inverseMap_approximates_smallBall {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z : ℂ} (hz : 0<z.im) :
    ApproximatesLinearOn (inverseMap a b T)
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv (inverseMap a b T) z))
      (closedBall z (z.im/100)) (‖deriv (inverseMap a b T) z‖₊/2) := by
  let f := inverseMap a b T
  let D := deriv f z
  have hd (v : ℂ) (hv : v∈closedBall z (z.im/100)) :
      HasFDerivWithinAt (fun w=>f w-D*w)
        (ContinuousLinearMap.toSpanSingleton ℂ (deriv f v-D)) (closedBall z (z.im/100)) v := by
    have hh := (inverseMap_hasStrictDerivAt ha b T
      (lt_of_lt_of_le (by positivity : 0<z.im/2) (smallBall_im_half hz hv))).hasDerivAt
    rw [←hh.deriv] at hh
    have h := hh.sub ((hasDerivAt_id v).const_mul D)
    simp only [mul_one] at h
    exact h.hasFDerivAt.hasFDerivWithinAt
  intro x hx y hy
  have hh := (convex_closedBall z (z.im/100)).norm_image_sub_le_of_norm_hasFDerivWithin_le hd
    (fun v hv=>by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using
      inverseMap_deriv_close_on_smallBall ha b T hz hv) hy hx
  convert! hh using 1
  · congr 1
    change f x-f y-(x-y)*D=f x-D*x-(f y-D*y)
    ring

 
def spanRightInverse (D : ℂ) (hD : D≠0) :
    (ContinuousLinearMap.toSpanSingleton ℂ D).NonlinearRightInverse where
  toFun w := w/D
  nnnorm := ‖D‖₊⁻¹
  bound' w := by simp only [norm_div,NNReal.coe_inv,coe_nnnorm]; exact le_of_eq (by ring)
  right_inv' w := by change (w/D)*D=w; exact div_mul_cancel₀ w hD

 

theorem inverseMap_inner_ball {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {z : ℂ} (hz : 0<z.im) :
    closedBall (inverseMap a b T z) (z.im*‖deriv (inverseMap a b T) z‖/200) ⊆
      inverseMap a b T '' closedBall z (z.im/100) := by
  have hh := (inverseMap_approximates_smallBall ha b T hz).surjOn_closedBall_of_nonlinearRightInverse
    (spanRightInverse _ (deriv_inverseMap_ne_zero ha b T hz))
    (by positivity : 0≤z.im/100) (Subset.rfl)
  have he : (((((spanRightInverse (deriv (inverseMap a b T) z)
      (deriv_inverseMap_ne_zero ha b T hz)).nnnorm:ℝ))⁻¹-
        (‖deriv (inverseMap a b T) z‖₊/2:ℝ≥0))*(z.im/100))=
      z.im*‖deriv (inverseMap a b T) z‖/200 := by
    simp only [spanRightInverse,NNReal.coe_inv,coe_nnnorm,inv_inv,NNReal.coe_div,NNReal.coe_ofNat]
    ring
  rw [he] at hh
  exact hh

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain LoewnerRestart FlowIdentification
open CenteredMoments KernelSimilarity ExactSLEGreen

 
def diskAt (w v : ℂ) : ℂ := (v-w)/(v-star w)

def centeredRegion (w : ℂ) (q : ℝ) : Set ℂ := {v | 0<v.im ∧ ‖diskAt w v‖≤q}

def subdiskReach (q : ℝ) : ℝ := 2*q/(1-q)
def subdiskHeight (q : ℝ) : ℝ := (1-q^2)/4
def subdiskDistortion (q : ℝ) : ℝ := Real.exp (3*subdiskReach q/subdiskHeight q)

lemma subdiskReach_nonneg {q : ℝ} (hq : 0≤q) (hq1 : q<1) : 0≤ subdiskReach q := by
  unfold subdiskReach
  positivity
lemma subdiskHeight_pos {q : ℝ} (hq : 0≤q) (hq1 : q<1) : 0<subdiskHeight q := by
  unfold subdiskHeight
  nlinarith
lemma subdiskHeight_le_one (q : ℝ) : subdiskHeight q≤1 := by
  unfold subdiskHeight
  nlinarith [sq_nonneg q]
lemma subdiskDistortion_pos (q : ℝ) : 0<subdiskDistortion q := Real.exp_pos _
lemma subdiskDistortion_ge_one {q : ℝ} (hq : 0≤q) (hq1 : q<1) : 1≤ subdiskDistortion q := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (mul_nonneg (by norm_num) (subdiskReach_nonneg hq hq1))
    (subdiskHeight_pos hq hq1).le

lemma diskAt_denominator_ne {w v : ℂ} (hw : 0<w.im) (hv : 0<v.im) : v-star w≠0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im,Complex.zero_im,sub_neg_eq_add] at hh
  linarith

lemma diskAt_affine {w : ℂ} (hw : 0<w.im) (v : ℂ) :
    diskAt w (affine (w.re:ℂ) w.im hw v)=(v-Complex.I)/(v+Complex.I) := by
  have hy : (w.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hwc : w=(w.re:ℂ)+(w.im:ℂ)*Complex.I := (Complex.re_add_im w).symm
  have hconj : star w=(w.re:ℂ)-(w.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  rw [diskAt,affine_apply]
  rw [show (w.re:ℂ)+(w.im:ℂ)*v-w=(w.im:ℂ)*(v-Complex.I) by
      apply Complex.ext <;> simp; ring,
    hconj,show (w.re:ℂ)+(w.im:ℂ)*v-((w.re:ℂ)-(w.im:ℂ)*Complex.I)=
      (w.im:ℂ)*(v+Complex.I) by ring,mul_div_mul_left _ _ hy]

lemma centeredRegion_bounds {w v : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 0≤q) (hq1 : q<1)
    (hv : v∈centeredRegion w q) :
    ‖v-w‖≤w.im*subdiskReach q ∧ w.im*subdiskHeight q≤v.im := by
  let z : UpperPlane := (upperAffine w.re w.im hw).symm ⟨v,hv.1⟩
  have he : affine (w.re:ℂ) w.im hw z.1=v := by
    exact congrArg Subtype.val ((upperAffine w.re w.im hw).apply_symm_apply ⟨v,hv.1⟩)
  have hz : ‖(z.1-Complex.I)/(z.1+Complex.I)‖≤q := by
    rw [←diskAt_affine hw z.1,he]
    exact hv.2
  have hb := cayley_subdisk_bounds q hq hq1 z hz
  have hn : ‖v-w‖=w.im*‖z.1-Complex.I‖ := by
    rw [←he,affine_apply,show (w.re:ℂ)+(w.im:ℂ)*z.1-w=(w.im:ℂ)*(z.1-Complex.I) by
      apply Complex.ext <;> simp; ring,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
  constructor
  · rw [hn]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm,subdiskReach] using hb.1) hw.le
  · rw [←he,affine_apply]
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      zero_mul,zero_add,add_zero]
    exact mul_le_mul_of_nonneg_left hb.2 hw.le

lemma smallBall_subset_centeredRegion {w : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 1/2≤q) :
    closedBall w (w.im/100) ⊆ centeredRegion w q := by
  intro v hv
  have hi := smallBall_im_half hw hv
  have hv0 : 0<v.im := lt_of_lt_of_le (by positivity : 0<w.im/2) hi
  refine ⟨hv0,?_⟩
  have hn : ‖v-w‖≤w.im/100 := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hden : w.im≤‖v-star w‖ := by
    apply le_trans _ (Complex.im_le_norm _)
    simp only [Complex.sub_im,Complex.star_def,Complex.conj_im,sub_neg_eq_add]
    linarith
  change ‖(v-w)/(v-star w)‖≤q
  rw [norm_div]
  exact ((div_le_div₀ (by positivity : 0≤w.im/100) hn hw hden).trans (by
    calc
      (w.im/100)/w.im=(1/100:ℝ) := by field_simp
      _ ≤ q := by linarith))

lemma centeredRegion_deriv_bounds {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w v : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 0≤q) (hq1 : q<1)
    (hv : v∈centeredRegion w q) :
    ‖deriv (inverseMap a b T) w‖/subdiskDistortion q≤‖deriv (inverseMap a b T) v‖ ∧
    ‖deriv (inverseMap a b T) v‖≤‖deriv (inverseMap a b T) w‖*subdiskDistortion q := by
  have hb := centeredRegion_bounds hw hq hq1 hv
  have hh := inverseMap_deriv_two_sided ha b T (mul_pos hw (subdiskHeight_pos hq hq1))
    (mul_le_of_le_one_right hw.le (subdiskHeight_le_one q)) hb.2 hb.1
  have he : (3/(w.im*subdiskHeight q))*(w.im*subdiskReach q)=3*subdiskReach q/subdiskHeight q := by
    field_simp
  rw [show -(3/(w.im*subdiskHeight q))*(w.im*subdiskReach q)=
      -((3/(w.im*subdiskHeight q))*(w.im*subdiskReach q)) by ring,he,Real.exp_neg] at hh
  simpa only [subdiskDistortion,div_eq_mul_inv] using hh

 
lemma centeredRegion_image_bound {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w v : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 0≤q) (hq1 : q<1)
    (hv : v∈centeredRegion w q) :
    ‖inverseMap a b T v-inverseMap a b T w‖≤
      subdiskReach q*subdiskDistortion q*(w.im*‖deriv (inverseMap a b T) w‖) := by
  have hb := centeredRegion_bounds hw hq hq1 hv
  let y : ℝ := w.im*subdiskHeight q
  have hy : 0<y := mul_pos hw (subdiskHeight_pos hq hq1)
  have hw' : y≤w.im := mul_le_of_le_one_right hw.le (subdiskHeight_le_one q)
  have hxy (t : ℝ) (ht : t∈Icc 0 1) : y≤(AffineMap.lineMap w v t).im :=
    lineMap_im_lower hw' hb.2 ht
  have hdist (t : ℝ) (ht : t∈Icc 0 1) : ‖AffineMap.lineMap w v t-w‖≤w.im*subdiskReach q := by
    rw [AffineMap.lineMap_apply]
    simp only [vadd_eq_add,vsub_eq_sub,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hb.1
  have he : (3/y)*(w.im*subdiskReach q)=3*subdiskReach q/subdiskHeight q := by
    dsimp [y]; field_simp
  have hd (t : ℝ) (ht : t∈Icc 0 1) :
      HasDerivAt (fun t : ℝ=>inverseMap a b T (AffineMap.lineMap w v t))
        (deriv (inverseMap a b T) (AffineMap.lineMap w v t)*(v-w)) t := by
    apply lineMap_hasDerivAt_complex_comp
    exact ((inverseMap_hasStrictDerivAt ha b T (hy.trans_le (hxy t ht))).hasDerivAt).differentiableAt.hasDerivAt
  have hbound (t : ℝ) (ht : t∈Icc 0 1) :
      ‖deriv (inverseMap a b T) (AffineMap.lineMap w v t)*(v-w)‖≤
      (‖deriv (inverseMap a b T) w‖*subdiskDistortion q)*‖v-w‖ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hh := (inverseMap_deriv_two_sided ha b T hy hw' (hxy t ht) (hdist t ht)).2
    rwa [he] at hh
  have hh := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht=>(hd t ht).hasDerivWithinAt) hbound
    (by norm_num : (0:ℝ)∈Icc 0 1) (by norm_num : (1:ℝ)∈Icc 0 1)
  simp only [AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,sub_zero,norm_one,mul_one] at hh
  exact hh.trans (by
    calc
      _ ≤ (‖deriv (inverseMap a b T) w‖*subdiskDistortion q)*(w.im*subdiskReach q) := mul_le_mul_of_nonneg_left hb.1
        (mul_nonneg (norm_nonneg _) (subdiskDistortion_pos q).le)
      _ = _ := by ring)

 

theorem inverseMap_centered_localization {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 1/2≤q) (hq1 : q<1) :
    closedBall (inverseMap a b T w) (w.im*‖deriv (inverseMap a b T) w‖/200) ⊆
      inverseMap a b T '' centeredRegion w q ∧
    inverseMap a b T '' centeredRegion w q ⊆ closedBall (inverseMap a b T w)
      (subdiskReach q*subdiskDistortion q*(w.im*‖deriv (inverseMap a b T) w‖)) := by
  refine ⟨(inverseMap_inner_ball ha b T hw).trans
    (image_mono (smallBall_subset_centeredRegion hw hq)),?_⟩
  rintro _ ⟨v,hv,rfl⟩
  simpa only [mem_closedBall,dist_eq_norm] using centeredRegion_image_bound ha b T hw (by linarith) hq1 hv

lemma diskAt_hasDerivAt {w v : ℂ} (hw : 0<w.im) (hv : 0<v.im) :
    HasDerivAt (diskAt w) (((2*w.im:ℝ):ℂ)*Complex.I/(v-star w)^2) v := by
  have hh := ((hasDerivAt_id v).sub_const w).div
    ((hasDerivAt_id v).sub_const (star w)) (diskAt_denominator_ne hw hv)
  convert! hh using 1
  simp only [id_eq,one_mul,mul_one]
  congr 1
  apply Complex.ext <;> simp; ring

lemma diskAt_deriv_norm {w v : ℂ} (hw : 0<w.im) (hv : 0<v.im) :
    ‖deriv (diskAt w) v‖=2*w.im/‖v-star w‖^2 := by
  rw [(diskAt_hasDerivAt hw hv).deriv,norm_div,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) hw),
    Complex.norm_I,mul_one]

lemma diskAt_deriv_bound {w v : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 0≤q) (hq1 : q<1)
    (hv : v∈centeredRegion w q) :
    2/((subdiskReach q+2)^2*w.im) ≤ ‖deriv (diskAt w) v‖ ∧
    ‖deriv (diskAt w) v‖ ≤ 2/w.im := by
  rw [diskAt_deriv_norm hw hv.1]
  have hb := centeredRegion_bounds hw hq hq1 hv
  have hn : w.im≤‖v-star w‖ := by
    apply le_trans _ (Complex.im_le_norm _)
    simp only [Complex.sub_im,Complex.star_def,Complex.conj_im,sub_neg_eq_add]
    linarith [hv.1]
  have hu : ‖v-star w‖≤w.im*(subdiskReach q+2) := by
    calc
      _ = ‖(v-w)+(w-star w)‖ := by congr 1; ring
      _ ≤ ‖v-w‖+‖w-star w‖ := norm_add_le _ _
      _ = ‖v-w‖+2*w.im := by
        rw [show w-star w=((2*w.im:ℝ):ℂ)*Complex.I by
          apply Complex.ext <;> simp; ring,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (mul_pos (by norm_num) hw),Complex.norm_I,mul_one]
      _ ≤ _ := by linarith [hb.1]
  have hq' : 0<subdiskReach q+2 := by linarith [subdiskReach_nonneg hq hq1]
  constructor
  · calc
      _ = 2*w.im/(w.im*(subdiskReach q+2))^2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (hw.trans_le hn)) (pow_le_pow_left₀ (norm_nonneg _) hu 2)
  · calc
      _ ≤ 2*w.im/w.im^2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hw) (pow_le_pow_left₀ hw.le hn 2)
      _ = _ := by field_simp

 

theorem centered_disk_deriv_ratio {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w v : ℂ} (hw : 0<w.im) {q : ℝ} (hq : 0≤q) (hq1 : q<1)
    (hv : v∈centeredRegion w q) :
    (w.im*‖deriv (inverseMap a b T) w‖)/(2*subdiskDistortion q) ≤
        ‖deriv (inverseMap a b T) v‖/‖deriv (diskAt w) v‖ ∧
    ‖deriv (inverseMap a b T) v‖/‖deriv (diskAt w) v‖ ≤
        (subdiskDistortion q*(subdiskReach q+2)^2/2)*(w.im*‖deriv (inverseMap a b T) w‖) := by
  have hf := centeredRegion_deriv_bounds ha b T hw hq hq1 hv
  have hg := diskAt_deriv_bound hw hq hq1 hv
  have hq' : 0<subdiskReach q+2 := by linarith [subdiskReach_nonneg hq hq1]
  have hlow : 0<2/((subdiskReach q+2)^2*w.im) := by positivity
  have hnorm : 0<‖deriv (diskAt w) v‖ := hlow.trans_le hg.1
  constructor
  · calc
      _ = (‖deriv (inverseMap a b T) w‖/subdiskDistortion q)/(2/w.im) := by field_simp
      _ ≤ _ := div_le_div₀ (norm_nonneg _) hf.1 hnorm hg.2
  · calc
      _ ≤ (‖deriv (inverseMap a b T) w‖*subdiskDistortion q)/(2/((subdiskReach q+2)^2*w.im)) :=
        div_le_div₀ (mul_nonneg (norm_nonneg _) (subdiskDistortion_pos q).le) hf.2 hlow hg.1
      _ = _ := by field_simp

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain ExactSLEGreen LoewnerRestart FlowIdentification

lemma centered_im_pos {a : ℝ} {b : GDriver} {t : ℝ≥0} {z : ℂ}
    (hz : alive a b.1 t z) : 0<(loewnerMap a b.1 t z-(b.1 t:ℂ)).im := by
  simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using loewnerMap_im_pos hz

lemma inverseMap_spatial_radius {a : ℝ} (ha : 0<a) (b : GDriver) (t : ℝ≥0)
    {z : ℂ} (hz : alive a b.1 t z) :
    (loewnerMap a b.1 t z-(b.1 t:ℂ)).im *
        ‖deriv (inverseMap a b t) (loewnerMap a b.1 t z-(b.1 t:ℂ))‖ =
      physicalRadius (actualState a b.1 t z) := by
  rw [deriv_inverseMap ha b t (centered_im_pos hz),inverseMap_centered a b t hz,
    norm_inv]
  have hd := norm_pos_iff.mpr (deriv_loewnerMap_ne_zero b.1.continuous hz)
  simp only [physicalRadius,actualState,Y_apply,J_apply,Real.exp_neg,Real.exp_log hd]

 

theorem radius_ball_subset_alive {a : ℝ} (ha : 0<a) (b : GDriver) (t : ℝ≥0)
    {z : ℂ} (hz : alive a b.1 t z) :
    closedBall z (physicalRadius (actualState a b.1 t z)/200) ⊆ {v | alive a b.1 t v} := by
  have hh := inverseMap_inner_ball ha b t (centered_im_pos hz)
  rw [inverseMap_spatial_radius ha b t hz,inverseMap_centered a b t hz] at hh
  intro v hv
  obtain ⟨w,hw,rfl⟩ := hh hv
  exact inverseMap_alive ha b t (lt_of_lt_of_le
    (div_pos (centered_im_pos hz) (by norm_num))
    (smallBall_im_half (centered_im_pos hz) hw))

 
theorem centered_localization_at_alive {a : ℝ} (ha : 0<a) (b : GDriver) (t : ℝ≥0)
    {z : ℂ} (hz : alive a b.1 t z) {q : ℝ} (hq : 1/2≤q) (hq1 : q<1) :
    closedBall z (physicalRadius (actualState a b.1 t z)/200) ⊆
        inverseMap a b t '' centeredRegion (loewnerMap a b.1 t z-(b.1 t:ℂ)) q ∧
    inverseMap a b t '' centeredRegion (loewnerMap a b.1 t z-(b.1 t:ℂ)) q ⊆
      closedBall z (subdiskReach q*subdiskDistortion q*physicalRadius (actualState a b.1 t z)) := by
  have hh := inverseMap_centered_localization ha b t (centered_im_pos hz) hq hq1
  rwa [inverseMap_spatial_radius ha b t hz,inverseMap_centered a b t hz] at hh

end SLEExactGauge.LoewnerGeometry
end
end

end OAI
