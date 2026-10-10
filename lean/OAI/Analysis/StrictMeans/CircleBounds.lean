import OAI.Analysis.StrictMeans.DyadicGap

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def horizontalQMean (y : ℝ) (hy : 0 < y) : C(DiskFamily, ℝ) :=
  (1/2:ℝ) • ∫ x in (-1:ℝ)..1, affineOperator (xyPoint x y hy) 1

lemma continuous_Q_slice (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => affineOperator (xyPoint x y hy) 1) :=
  (continuous_affineOperator_strong 1).comp (continuous_xyPoint continuous_id continuous_const _)

lemma horizontalQMean_apply (y : ℝ) (hy : 0 < y) (f : DiskFamily) :
    horizontalQMean y hy f = (1/2:ℝ) * ∫ x in (-1:ℝ)..1, ‖halfPlaneQ f (xyPoint x y hy)‖ := by
  have he := (ContinuousMap.evalCLM ℝ f).intervalIntegral_comp_comm (μ := volume)
    ((continuous_Q_slice y hy).intervalIntegrable (-1) 1)
  simp only [ContinuousMap.evalCLM_apply, affineOperator_apply,
    ContinuousMap.one_apply, mul_one] at he
  change (1/2:ℝ) * _ = _
  rw [← he]

lemma continuous_Q_slice_apply (f : DiskFamily) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => ‖halfPlaneQ f (xyPoint x y hy)‖) := by
  have hh := (ContinuousMap.evalCLM ℝ f).continuous.comp (continuous_Q_slice y hy)
  change Continuous (fun x => (ContinuousMap.evalCLM ℝ f) (affineOperator (xyPoint x y hy) 1)) at hh
  simpa only [ContinuousMap.evalCLM_apply, affineOperator_apply, ContinuousMap.one_apply, mul_one] using hh

lemma dyadic_left_xy (x y : ℝ) (hy : 0 < y) :
    affineProduct dyadicLeft (xyPoint x y hy) =
      xyPoint ((1/2:ℝ)*x-1/2) (y/2) (half_pos hy) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicLeft, xyPoint]
  ring

lemma dyadic_right_xy (x y : ℝ) (hy : 0 < y) :
    affineProduct dyadicRight (xyPoint x y hy) =
      xyPoint ((1/2:ℝ)*x+1/2) (y/2) (half_pos hy) := by
  apply UpperHalfPlane.ext
  simp [coe_affineProduct, affineAt, dyadicRight, xyPoint]
  ring

lemma horizontalQMean_half (y : ℝ) (hy : 0 < y) :
    horizontalQMean (y/2) (half_pos hy) = dyadicOperator (horizontalQMean y hy) := by
  let A : ℝ → C(DiskFamily, ℝ) := fun x => affineOperator (xyPoint x (y/2) (half_pos hy)) 1
  have hA : Continuous A := continuous_Q_slice (y/2) (half_pos hy)
  have hleft : (∫ x in (-1:ℝ)..1,
      affineOperator dyadicLeft (affineOperator (xyPoint x y hy) 1)) =
        (2:ℝ) • ∫ x in (-1:ℝ)..0, A x := by
    simp_rw [← mul_apply_eq_comp, affineOperator_mul, dyadic_left_xy]
    have hh := intervalIntegral.integral_comp_mul_add (a := (-1:ℝ)) (b := 1) A
      (by norm_num : (1/2:ℝ) ≠ 0) (-1/2)
    norm_num only at hh
    simpa only [sub_eq_add_neg] using hh
  have hright : (∫ x in (-1:ℝ)..1,
      affineOperator dyadicRight (affineOperator (xyPoint x y hy) 1)) =
        (2:ℝ) • ∫ x in (0:ℝ)..1, A x := by
    simp_rw [← mul_apply_eq_comp, affineOperator_mul, dyadic_right_xy]
    have hh := intervalIntegral.integral_comp_mul_add (a := (-1:ℝ)) (b := 1) A
      (by norm_num : (1/2:ℝ) ≠ 0) (1/2)
    norm_num only at hh
    simpa only [sub_eq_add_neg] using hh
  unfold horizontalQMean dyadicOperator
  rw [smul_apply, add_apply,
    map_smul, map_smul,
    ← (affineOperator dyadicLeft).intervalIntegral_comp_comm ((continuous_Q_slice y hy).intervalIntegrable _ _),
    ← (affineOperator dyadicRight).intervalIntegral_comp_comm ((continuous_Q_slice y hy).intervalIntegrable _ _),
    hleft, hright, smul_smul, smul_smul]
  norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (hA.intervalIntegrable (-1) 0)
    (hA.intervalIntegrable 0 1)]
  exact smul_add _ _ _

lemma horizontalQMean_dyadic (n : ℕ) :
    horizontalQMean (dyadicHeight n) (dyadicHeight_pos n) =
      (dyadicOperator^n) (horizontalQMean 1 zero_lt_one) := by
  induction n with
  | zero => simp [dyadicHeight]
  | succ n ih =>
    simp only [dyadicHeight_succ]
    rw [horizontalQMean_half (dyadicHeight n) (dyadicHeight_pos n), ih, pow_succ', mul_apply_eq_comp]

lemma horizontalQMean_bound (n : ℕ) (f : DiskFamily) :
    (∫ x in (-1:ℝ)..1, ‖halfPlaneQ f (xyPoint x (dyadicHeight n) (dyadicHeight_pos n))‖) ≤
      (2 * ‖horizontalQMean 1 zero_lt_one‖) * ‖dyadicOperator^n‖ := by
  have hh := (horizontalQMean (dyadicHeight n) (dyadicHeight_pos n)).norm_coe_le_norm f
  have hb := (dyadicOperator^n).le_opNorm (horizontalQMean 1 zero_lt_one)
  rw [← horizontalQMean_dyadic] at hb
  rw [horizontalQMean_apply, Real.norm_eq_abs] at hh
  have hle := (le_abs_self _).trans (hh.trans hb)
  nlinarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def arcDenom (r t : ℝ) : ℝ := 1 + 2*r*Real.cos t + r^2
def arcX (r t : ℝ) : ℝ := 2*r*Real.sin t / arcDenom r t
def arcY (r t : ℝ) : ℝ := (1-r^2) / arcDenom r t
def arcXDeriv (r t : ℝ) : ℝ :=
  (2*r*(1+r^2)*Real.cos t+4*r^2)/(arcDenom r t)^2

lemma arcDenom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    0 < arcDenom r t := by
  have hh := mul_nonneg hr0 (show 0 ≤ 1+Real.cos t by linarith [Real.neg_one_le_cos t])
  have hs := sq_pos_of_pos (show 0 < 1-r by linarith)
  dsimp [arcDenom]
  nlinarith

lemma arcDenom_le_four {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (t : ℝ) :
    arcDenom r t ≤ 4 := by
  have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hr0
  dsimp [arcDenom]
  nlinarith

lemma arcDenom_ge_one {r : ℝ} (hr0 : 0 ≤ r) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : 1 ≤ arcDenom r t := by
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], ht.2⟩
  have hh := mul_nonneg hr0 hc
  dsimp [arcDenom]
  nlinarith

lemma arcX_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (arcX r) := by
  exact ((continuous_const.mul continuous_const).mul Real.continuous_sin).div
    ((continuous_const.add ((continuous_const.mul continuous_const).mul Real.continuous_cos)).add
      continuous_const) (fun t => (arcDenom_pos hr0 hr t).ne')

lemma arcY_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (arcY r) := by
  exact continuous_const.div
    ((continuous_const.add ((continuous_const.mul continuous_const).mul Real.continuous_cos)).add
      continuous_const) (fun t => (arcDenom_pos hr0 hr t).ne')

lemma arcX_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    HasDerivAt (arcX r) (arcXDeriv r t) t := by
  have hn := (Real.hasDerivAt_sin t).const_mul (2*r)
  have hd := (((Real.hasDerivAt_cos t).const_mul (2*r)).const_add 1).add_const (r^2)
  have hh : HasDerivAt (arcX r)
      ((2*r*Real.cos t * arcDenom r t - 2*r*Real.sin t*(2*r*(-Real.sin t))) / (arcDenom r t)^2) t :=
    hn.div hd (arcDenom_pos hr0 hr t).ne'
  convert hh using 1
  dsimp [arcXDeriv,arcDenom]
  congr 1
  linear_combination -(4*r^2)*(Real.sin_sq_add_cos_sq t)

lemma arcXDeriv_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (arcXDeriv r) := by
  exact ((continuous_const.mul Real.continuous_cos).add continuous_const).div
    (((continuous_const.add ((continuous_const.mul continuous_const).mul Real.continuous_cos)).add
      continuous_const).pow 2) (fun t => pow_ne_zero _ (arcDenom_pos hr0 hr t).ne')

lemma arcXDeriv_lower {r : ℝ} (hr0 : 1/2 ≤ r) (hr : r < 1) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : (1/16:ℝ) ≤ arcXDeriv r t := by
  have hrp : 0 ≤ r := by linarith
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], ht.2⟩
  have hd := arcDenom_pos hrp hr t
  have hu := arcDenom_le_four hrp hr.le t
  have hn : 0 ≤ 2*r*(1+r^2)*Real.cos t := by positivity
  rw [arcXDeriv, le_div_iff₀ (sq_pos_of_pos hd)]
  nlinarith

lemma arcX_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : -1 ≤ arcX r t ∧ arcX r t ≤ 1 := by
  have hd := arcDenom_pos hr0 hr t
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], ht.2⟩
  have hc' := mul_nonneg hr0 hc
  have ha := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hr0
  have hb := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hr0
  constructor
  · rw [arcX, le_div_iff₀ hd]
    dsimp [arcDenom]
    nlinarith [sq_nonneg (1-r)]
  · rw [arcX, div_le_iff₀ hd]
    dsimp [arcDenom]
    nlinarith [sq_nonneg (1-r)]

lemma arcY_pos {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) : 0 < arcY r t := by
  apply div_pos _ (arcDenom_pos hr0 hr t)
  nlinarith

lemma arcY_scale_bounds {r v : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hv : v ≤ 1-r) (hrv : 1-r ≤ 2*v) {t : ℝ}
    (ht : t ∈ Icc (-(Real.pi/2)) (Real.pi/2)) : v/4 ≤ arcY r t ∧ arcY r t ≤ 4*v := by
  have hvp : 0 < v := by linarith
  have hd := arcDenom_pos hr0 hr t
  have hu := arcDenom_le_four hr0 hr.le t
  have hl := arcDenom_ge_one hr0 ht
  have hprod := mul_le_mul_of_nonneg_left hu hvp.le
  have hprod' := mul_le_mul_of_nonneg_left hl hvp.le
  constructor
  · rw [arcY, le_div_iff₀ hd]
    nlinarith
  · rw [arcY, div_le_iff₀ hd]
    nlinarith [sq_nonneg (1-r)]

lemma cayley_leftArc (r t : ℝ) :
    cayleyToHalfPlane (-(r:ℂ)*Complex.exp ((t:ℂ)*I)) =
      (arcX r t:ℂ) + (arcY r t:ℂ)*I := by
  apply Complex.ext
  all_goals simp only [cayleyToHalfPlane, Complex.div_re, Complex.div_im,
    Complex.exp_mul_I, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.normSq_apply,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, neg_zero, sub_zero]
  all_goals dsimp [arcX, arcY, arcDenom]
  all_goals have hs := congrArg (fun a : ℝ => r^2*a) (Real.sin_sq_add_cos_sq t)
  all_goals have hd : (1 - -r * Real.cos t) * (1 - -r * Real.cos t) +
      (0 - -r * Real.sin t) * (0 - -r * Real.sin t) = 1 + 2*r*Real.cos t + r^2 := by nlinarith [hs]
  all_goals rw [hd]
  · rw [← add_div]
    congr 1
    ring
  · rw [← sub_div]
    congr 1
    nlinarith [hs]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma uniform_vertical_Q_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : DiskFamily) (s : ℝ) (hs : 0 < s),
      1/4 ≤ s → s ≤ 4 → ‖halfPlaneQ f (xyPoint 0 s hs)‖ ≤ K := by
  let X := DiskFamily × Icc (1/4:ℝ) 4
  let W : C(X, ℝ) := ⟨fun p => ‖halfPlaneQ p.1 (xyPoint 0 p.2 (by have hh := p.2.property.1; linarith))‖,
    (continuous_halfPlaneQ.comp (continuous_fst.prodMk
      ((continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul_const I)).upperHalfPlaneMk _))).norm⟩
  refine ⟨‖W‖+1, by positivity, ?_⟩
  intro f s hs hlo hhi
  have hh := W.norm_coe_le_norm (f,⟨s,hlo,hhi⟩)
  change ‖‖halfPlaneQ f (xyPoint 0 s hs)‖‖ ≤ ‖W‖ at hh
  rw [norm_norm] at hh
  linarith

lemma vertical_Q_comparison {K : ℝ}
    (hK : ∀ (f : DiskFamily) (s : ℝ) (hs : 0 < s),
      1/4 ≤ s → s ≤ 4 → ‖halfPlaneQ f (xyPoint 0 s hs)‖ ≤ K)
    (f : DiskFamily) (x y v : ℝ) (hy : 0 < y) (hv : 0 < v)
    (hlo : v/4 ≤ y) (hhi : y ≤ 4*v) :
    ‖halfPlaneQ f (xyPoint x y hy)‖ ≤ K * ‖halfPlaneQ f (xyPoint x v hv)‖ := by
  have hp : 0 < y/v := div_pos hy hv
  have hlow : 1/4 ≤ y/v := (le_div_iff₀ hv).mpr (by linarith)
  have hupp : y/v ≤ 4 := (div_le_iff₀ hv).mpr hhi
  have he : affineProduct (xyPoint x v hv) (xyPoint 0 (y/v) hp) = xyPoint x y hy := by
    simp only [affineProduct_xyPoint,mul_zero,add_zero,mul_div_cancel₀ _ hv.ne']
  have hh := hK (rebase f (xyPoint x v hv)) (y/v) hp hlow hupp
  rw [halfPlaneQ_rebase,he,norm_div] at hh
  exact (div_le_iff₀ (norm_pos_iff.mpr (halfPlaneQ_ne_zero f _))).mp hh

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma arc_integral_change_bound (f : DiskFamily) {r v : ℝ}
    (hr0 : 1/2 ≤ r) (hr : r < 1) (hv : 0 < v) :
    (∫ t in -(Real.pi/2)..(Real.pi/2),
      ‖halfPlaneQ f (xyPoint (arcX r t) v hv)‖) ≤
      16 * ∫ x in (-1:ℝ)..1, ‖halfPlaneQ f (xyPoint x v hv)‖ := by
  let g : ℝ → ℝ := fun x => ‖halfPlaneQ f (xyPoint x v hv)‖
  have hg : Continuous g := continuous_Q_slice_apply f v hv
  have hrp : 0 ≤ r := by linarith
  have hab : -(Real.pi/2) ≤ Real.pi/2 := by linarith [Real.pi_pos]
  have hxc := arcX_continuous hrp hr
  have hdc := arcXDeriv_continuous hrp hr
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := -(Real.pi/2)) (b := Real.pi/2)
    (fun t _ => arcX_hasDerivAt hrp hr t) hdc.continuousOn hg
  have hmono : (∫ t in -(Real.pi/2)..(Real.pi/2), g (arcX r t)) ≤
      ∫ t in -(Real.pi/2)..(Real.pi/2), 16 * (g (arcX r t) * arcXDeriv r t) := by
    apply intervalIntegral.integral_mono_on hab
      ((hg.comp hxc).intervalIntegrable _ _)
      ((continuous_const.mul ((hg.comp hxc).mul hdc)).intervalIntegrable _ _)
    intro t ht
    have hd := arcXDeriv_lower hr0 hr ht
    have hp : 0 ≤ g (arcX r t) := norm_nonneg _
    change g (arcX r t) ≤ 16 * (g (arcX r t) * arcXDeriv r t)
    nlinarith
  simp only [Function.comp_apply] at hsub
  rw [intervalIntegral.integral_const_mul, hsub] at hmono
  have hxle : arcX r (-(Real.pi/2)) ≤ arcX r (Real.pi/2) := by
    have hh := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-(Real.pi/2)) (Real.pi/2))
      hxc.continuousOn (fun t _ => (arcX_hasDerivAt hrp hr t).hasDerivWithinAt)
      (fun t ht => (by
        exact le_trans (by norm_num : (0:ℝ) ≤ 1/16) (arcXDeriv_lower hr0 hr (interior_subset ht))))
    exact hh ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have he0 := arcX_bounds hrp hr (show -(Real.pi/2) ∈ Icc (-(Real.pi/2)) (Real.pi/2) from ⟨le_rfl,hab⟩)
  have he1 := arcX_bounds hrp hr (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) from ⟨hab,le_rfl⟩)
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_interval he0.1 hxle he1.2
      (ae_of_all _ (fun x => norm_nonneg _)) (hg.intervalIntegrable (-1) 1)) (by norm_num))

lemma inverse_disk_deriv_cayley_bound (f : DiskFamily) (z : UpperHalfPlane) :
    ‖deriv (diskExtension f.val) (cayleyToDisk z)‖⁻¹ ≤ 4 * ‖halfPlaneQ f z‖ := by
  have hd := halfPlaneFunction_deriv f z.im_pos
  have hn : ‖deriv (halfPlaneFunction f) z‖ =
      4 * ‖deriv (diskExtension f.val) (cayleyToDisk z)‖ / ‖(z:ℂ)+I‖^2 := by
    rw [hd]
    simp only [norm_mul,norm_div,norm_pow,Complex.norm_I,norm_ofNat,mul_one]
    ring
  have hsq : 1 ≤ ‖(z:ℂ)+I‖^2 := by
    have hi := Complex.abs_im_le_norm ((z:ℂ)+I)
    have hz : 0 < (z:ℂ).im := z.im_pos
    simp only [Complex.add_im,Complex.I_im] at hi
    have hl := (le_abs_self _).trans hi
    nlinarith [norm_nonneg ((z:ℂ)+I)]
  have hp : 0 < ‖deriv (diskExtension f.val) (cayleyToDisk z)‖ :=
    norm_pos_iff.mpr (diskFamily_derivative_ne_zero f ⟨_,cayleyToDisk_mem z.im_pos⟩)
  simp only [halfPlaneQ,norm_inv,hn]
  rw [inv_div]
  field_simp
  exact hsq

lemma half_arc_inverse_bound {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ (f : DiskFamily) (s : ℝ) (hs : 0 < s),
      1/4 ≤ s → s ≤ 4 → ‖halfPlaneQ f (xyPoint 0 s hs)‖ ≤ K)
    (f : DiskFamily) {r v : ℝ} (hr0 : 1/2 ≤ r) (hr : r < 1)
    (hv : v ≤ 1-r) (hrv : 1-r ≤ 2*v) :
    (∫ t in -(Real.pi/2)..(Real.pi/2),
      ‖deriv (diskExtension f.val) (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹) ≤
      64*K * ∫ x in (-1:ℝ)..1,
        ‖halfPlaneQ f (xyPoint x v (by linarith))‖ := by
  have hrp : 0 ≤ r := by linarith
  have hvp : 0 < v := by linarith
  let γ : ℝ → UpperHalfPlane := fun t => xyPoint (arcX r t) (arcY r t) (arcY_pos hrp hr t)
  have hcγ : Continuous γ :=
    ((Complex.continuous_ofReal.comp (arcX_continuous hrp hr)).add
      ((Complex.continuous_ofReal.comp (arcY_continuous hrp hr)).mul_const I)).upperHalfPlaneMk _
  have he (t : ℝ) : cayleyToDisk (γ t) = -(r:ℂ)*Complex.exp ((t:ℂ)*I) := by
    rw [show (γ t : ℂ) = cayleyToHalfPlane (-(r:ℂ)*Complex.exp ((t:ℂ)*I)) from
      (cayley_leftArc r t).symm]
    apply cayleyToDisk_toHalfPlane
    simp only [mem_ball,dist_zero_right,norm_mul,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hrp,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact hr
  have hcont : Continuous (fun t : ℝ => ‖deriv (diskExtension f.val)
      (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹) := by
    simp_rw [← he]
    exact ((continuous_diskFamily_derivative.comp
      (continuous_const.prodMk (cayleyDiskMap.continuous.comp hcγ))).norm).inv₀
        (fun t => norm_ne_zero_iff.mpr (diskFamily_derivative_ne_zero f _))
  have hab : -(Real.pi/2) ≤ Real.pi/2 := by linarith [Real.pi_pos]
  have haux : Continuous (fun t => ‖halfPlaneQ f (xyPoint (arcX r t) v hvp)‖) :=
    (continuous_Q_slice_apply f v hvp).comp (arcX_continuous hrp hr)
  have hb : (∫ t in -(Real.pi/2)..(Real.pi/2),
      ‖deriv (diskExtension f.val) (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹) ≤
      ∫ t in -(Real.pi/2)..(Real.pi/2),
        (4*K) * ‖halfPlaneQ f (xyPoint (arcX r t) v hvp)‖ := by
    apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
      ((continuous_const.mul haux).intervalIntegrable _ _)
    intro t ht
    rw [← he]
    refine (inverse_disk_deriv_cayley_bound f (γ t)).trans ?_
    change 4 * ‖halfPlaneQ f (γ t)‖ ≤ (4*K)*‖halfPlaneQ f (xyPoint (arcX r t) v hvp)‖
    have hs := arcY_scale_bounds hrp hr hv hrv ht
    have hcmp := vertical_Q_comparison hK f (arcX r t) (arcY r t) v
      (arcY_pos hrp hr t) hvp hs.1 hs.2
    exact le_trans (mul_le_mul_of_nonneg_left hcmp (by norm_num)) (le_of_eq (by ring))
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (arc_integral_change_bound f hr0 hr hvp)
      (show 0 ≤ 4*K by positivity)
    convert hh using 1
    ring)

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

def diskNegateMap (f : C(UnitDisk,ℂ)) : C(UnitDisk,ℂ) :=
  ⟨fun z => -f ⟨-z,by simpa only [mem_ball,dist_zero_right,norm_neg] using z.property⟩,
    (f.continuous.comp ((continuous_subtype_val.neg).subtype_mk _)).neg⟩

lemma diskNegateMap_extension (f : C(UnitDisk,ℂ)) (z : ℂ) :
    diskExtension (diskNegateMap f) z = -diskExtension f (-z) := by
  classical
  by_cases hz : z ∈ ball (0:ℂ) 1
  · have hm : -z ∈ ball (0:ℂ) 1 := by simpa using hz
    simp only [diskExtension,dite_eq_left hz,dite_eq_left hm]
    rfl
  · have hm : -z ∉ ball (0:ℂ) 1 := by simpa using hz
    simp only [diskExtension,dite_eq_right hz,dite_eq_right hm,neg_zero]

lemma diskNegateMap_hasDerivAt (f : DiskFamily) {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    HasDerivAt (diskExtension (diskNegateMap f.val)) (deriv (diskExtension f.val) (-z)) z := by
  have hm : -z ∈ ball (0:ℂ) 1 := by simpa using hz
  have hh := ((f.property.1.differentiableAt (isOpen_ball.mem_nhds hm)).hasDerivAt.comp z
    (hasDerivAt_id z).neg).neg
  simp only [mul_neg,mul_one,neg_neg] at hh
  rw [show diskExtension (diskNegateMap f.val) = (fun w => -diskExtension f.val (-w)) from
    funext (diskNegateMap_extension f.val)]
  exact hh

def diskNegateFamily (f : DiskFamily) : DiskFamily := ⟨diskNegateMap f.val, by
  refine ⟨fun z hz => (diskNegateMap_hasDerivAt f hz).differentiableAt.differentiableWithinAt,
    ?_, ?_, ?_⟩
  · intro z hz w hw he
    simp only [diskNegateMap_extension,neg_inj] at he
    exact neg_injective (f.property.2.1 (by simpa using hz) (by simpa using hw) he)
  · simp [diskNegateMap_extension,f.property.2.2.1]
  · simpa only [neg_zero,f.property.2.2.2] using
      (diskNegateMap_hasDerivAt f (mem_ball_self zero_lt_one)).deriv⟩

def circleInverseDensity (f : DiskFamily) (r t : ℝ) : ℝ :=
  ‖deriv (diskExtension f.val) ((r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹

def leftArcInverseDensity (f : DiskFamily) (r t : ℝ) : ℝ :=
  ‖deriv (diskExtension f.val) (-(r:ℂ)*Complex.exp ((t:ℂ)*I))‖⁻¹

lemma circlePoint_mem_disk {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    (r:ℂ)*Complex.exp ((t:ℂ)*I) ∈ ball (0:ℂ) 1 := by
  simpa only [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hr0,Complex.norm_exp_ofReal_mul_I,mul_one] using hr

lemma circleInverseDensity_continuous (f : DiskFamily) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) : Continuous (circleInverseDensity f r) := by
  have hp : Continuous (fun t : ℝ => (⟨(r:ℂ)*Complex.exp ((t:ℂ)*I),
      circlePoint_mem_disk hr0 hr t⟩ : UnitDisk)) :=
    (continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const I))).subtype_mk _
  exact (continuous_diskFamily_derivative.comp (continuous_const.prodMk hp)).norm.inv₀
    (fun t => norm_ne_zero_iff.mpr (diskFamily_derivative_ne_zero f _))

lemma circleInverseDensity_periodic (f : DiskFamily) (r : ℝ) :
    Function.Periodic (circleInverseDensity f r) (2*Real.pi) := by
  intro t
  unfold circleInverseDensity
  congr 3
  push_cast
  rw [add_mul,Complex.exp_add]
  have hh : Complex.exp (((2:ℂ)*Real.pi)*I) = 1 := by
    convert Complex.exp_two_pi_mul_I using 1
  rw [hh,mul_one]

lemma circleInverseDensity_shift_pi (f : DiskFamily) (r t : ℝ) :
    circleInverseDensity f r (t+Real.pi) = leftArcInverseDensity f r t := by
  unfold circleInverseDensity leftArcInverseDensity
  congr 3
  push_cast
  rw [add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
  ring

lemma leftArcInverseDensity_negate (f : DiskFamily) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (t : ℝ) :
    leftArcInverseDensity (diskNegateFamily f) r t = circleInverseDensity f r t := by
  unfold leftArcInverseDensity circleInverseDensity
  change ‖deriv (diskExtension (diskNegateMap f.val)) _‖⁻¹ = _
  have hm : -(r:ℂ)*Complex.exp ((t:ℂ)*I) ∈ ball (0:ℂ) 1 := by
    simpa only [neg_mul,mem_ball,dist_zero_right,norm_neg] using circlePoint_mem_disk hr0 hr t
  rw [(diskNegateMap_hasDerivAt f hm).deriv]
  simp only [neg_mul,neg_neg]

lemma wholeCircle_eq_two_left_arcs (f : DiskFamily) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) :
    (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) =
      (∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity f r t) +
      ∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity (diskNegateFamily f) r t := by
  have hc := circleInverseDensity_continuous f hr0 hr
  simp_rw [leftArcInverseDensity_negate f hr0 hr]
  have hp := (circleInverseDensity_periodic f r).intervalIntegral_add_eq
    (-Real.pi) (-(Real.pi/2))
  have hshift := intervalIntegral.integral_comp_add_right
    (circleInverseDensity f r) Real.pi (a := -(Real.pi/2)) (b := Real.pi/2)
  simp only [circleInverseDensity_shift_pi] at hshift
  have he1 : -Real.pi+2*Real.pi = Real.pi := by ring
  have he2 : -(Real.pi/2)+Real.pi = Real.pi/2 := by ring
  have he3 : Real.pi/2+Real.pi = -(Real.pi/2)+2*Real.pi := by ring
  rw [he1] at hp
  rw [he2,he3] at hshift
  rw [hp,← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),← hshift]
  exact add_comm _ _

lemma whole_circle_dyadic_operator_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DiskFamily) (r : ℝ) (n : ℕ),
      1/2 ≤ r → r < 1 → dyadicHeight n ≤ 1-r → 1-r ≤ 2*dyadicHeight n →
      (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) ≤ C * ‖dyadicOperator^n‖ := by
  obtain ⟨K,hK0,hK⟩ := uniform_vertical_Q_bound
  let A := 2*‖horizontalQMean 1 zero_lt_one‖+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨128*K*A,by positivity,?_⟩
  intro f r n hr0 hr hv hrv
  have h0 := half_arc_inverse_bound hK0 hK f hr0 hr hv hrv
  have h1 := half_arc_inverse_bound hK0 hK (diskNegateFamily f) hr0 hr hv hrv
  have hb0 := horizontalQMean_bound n f
  have hb1 := horizontalQMean_bound n (diskNegateFamily f)
  have hb0' := h0.trans (mul_le_mul_of_nonneg_left hb0 (show 0 ≤ 64*K by positivity))
  have hb1' := h1.trans (mul_le_mul_of_nonneg_left hb1 (show 0 ≤ 64*K by positivity))
  rw [wholeCircle_eq_two_left_arcs f (by linarith) hr]
  change (∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity f r t) ≤ _ at hb0'
  change (∫ t in -(Real.pi/2)..Real.pi/2, leftArcInverseDensity (diskNegateFamily f) r t) ≤ _ at hb1'
  have hs := add_le_add hb0' hb1'
  refine hs.trans ?_
  dsimp [A]
  nlinarith [mul_nonneg hK0.le (norm_nonneg (dyadicOperator^n))]

end
end StrictInverseFirstPower

end

end OAI
