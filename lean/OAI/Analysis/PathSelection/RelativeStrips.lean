import Mathlib
import OAI.Analysis.PathSelection.ClockInverses

namespace OAI

/-! Derivative growth, relative strips and inverse clock ratios. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma real_log_derivative_bound {f g : ℝ → ℝ} {q : ℝ}
    (hf : ∀ᶠ t : ℝ in atTop,DifferentiableAt ℝ f t ∧ 0<f t)
    (hg : ∀ᶠ t : ℝ in atTop,DifferentiableAt ℝ g t ∧ 0<g t)
    (hd : ∀ᶠ t : ℝ in atTop,deriv f t/f t-q*(deriv g t/g t)≤0) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in atTop,f t≤C*(g t)^q := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hf.and (hg.and hd))
  let L : ℝ → ℝ := fun t => Real.log (f t)-q*Real.log (g t)
  have hL (t : ℝ) (ht : t∈Ici T) :
      HasDerivAt L (deriv f t/f t-q*(deriv g t/g t)) t :=
    ((hT t ht).1.1.hasDerivAt.log (hT t ht).1.2.ne').sub
      (((hT t ht).2.1.1.hasDerivAt.log (hT t ht).2.1.2.ne').const_mul q)
  have hanti : AntitoneOn L (Ici T) := antitoneOn_of_deriv_nonpos (convex_Ici T)
    (fun t ht => (hL t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hL t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hL t (interior_subset ht)).deriv]; exact (hT t (interior_subset ht)).2.2)
  refine ⟨Real.exp (L T),Real.exp_pos _,?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  have hh := hanti (show T∈Ici T by simp) ht ht
  have hft := (hT t ht).1.2
  have hgt := (hT t ht).2.1.2
  calc
    f t = Real.exp (Real.log (f t)) := (Real.exp_log hft).symm
    _ ≤ Real.exp (L T+q*Real.log (g t)) := Real.exp_le_exp.mpr (by dsimp [L] at hh; linarith)
    _ = Real.exp (L T)*(g t)^q := by rw [Real.exp_add,Real.rpow_def_of_pos hgt]; congr 2; ring

lemma complex_re_log_derivative {F : ℂ → ℂ} {t : ℝ}
    (ha : AnalyticAt ℂ F (t:ℂ)) (hr : (F (t:ℂ)).im=0) :
    DifferentiableAt ℝ (fun s : ℝ => (F (s:ℂ)).re) t ∧
      deriv (fun s : ℝ => (F (s:ℂ)).re) t/(F (t:ℂ)).re=(deriv F (t:ℂ)/F (t:ℂ)).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ha.differentiableAt.hasDerivAt.comp_ofReal
  change HasDerivAt (fun s : ℝ => (F (s:ℂ)).re) (deriv F (t:ℂ)).re t at hd
  refine ⟨hd.differentiableAt,?_⟩
  rw [hd.deriv,show F (t:ℂ)=((F (t:ℂ)).re:ℂ) from Complex.ext rfl (by simpa using hr)]
  simp only [Complex.ofReal_re,Complex.div_ofReal_re]

theorem complex_log_derivative_power_bound {F H : ℂ → ℂ} {a b q : ℝ}
    (hgap : a<q*b)
    (hFa : ∀ᶠ t : ℝ in atTop,AnalyticAt ℂ F (t:ℂ))
    (hHa : ∀ᶠ t : ℝ in atTop,AnalyticAt ℂ H (t:ℂ))
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFd : Tendsto (fun t : ℝ => deriv F (t:ℂ)/F (t:ℂ)) atTop (𝓝 (a:ℂ)))
    (hHd : Tendsto (fun t : ℝ => deriv H (t:ℂ)/H (t:ℂ)) atTop (𝓝 (b:ℂ))) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤C*((H (t:ℂ)).re)^q := by
  have hFreal : ∀ᶠ t : ℝ in atTop,DifferentiableAt ℝ (fun s : ℝ => (F (s:ℂ)).re) t ∧
      0<(F (t:ℂ)).re ∧ deriv (fun s : ℝ => (F (s:ℂ)).re) t/(F (t:ℂ)).re=(deriv F (t:ℂ)/F (t:ℂ)).re := by
    filter_upwards [hFa,hFr] with t ha hr
    exact ⟨(complex_re_log_derivative ha hr.1).1,hr.2,(complex_re_log_derivative ha hr.1).2⟩
  have hHreal : ∀ᶠ t : ℝ in atTop,DifferentiableAt ℝ (fun s : ℝ => (H (s:ℂ)).re) t ∧
      0<(H (t:ℂ)).re ∧ deriv (fun s : ℝ => (H (s:ℂ)).re) t/(H (t:ℂ)).re=(deriv H (t:ℂ)/H (t:ℂ)).re := by
    filter_upwards [hHa,hHr] with t ha hr
    exact ⟨(complex_re_log_derivative ha hr.1).1,hr.2,(complex_re_log_derivative ha hr.1).2⟩
  apply real_log_derivative_bound (hFreal.mono fun _ h => ⟨h.1,h.2.1⟩)
    (hHreal.mono fun _ h => ⟨h.1,h.2.1⟩)
  have ht := ((Complex.continuous_re.tendsto (a:ℂ)).comp hFd).sub
    (((Complex.continuous_re.tendsto (b:ℂ)).comp hHd).const_mul q)
  simp only [Complex.ofReal_re] at ht
  have hn := ht.eventually (eventually_lt_nhds (show a-q*b<0 by linarith))
  filter_upwards [hFreal,hHreal,hn] with t hf hh hn
  rw [hf.2.2,hh.2.2]
  exact hn.le

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma unbounded_log_exponent_order {F H : ℂ → ℂ} {a b : ℝ}
    (hb : 0≤b)
    (hFa : ∀ᶠ t : ℝ in atTop,AnalyticAt ℂ F (t:ℂ))
    (hHa : ∀ᶠ t : ℝ in atTop,AnalyticAt ℂ H (t:ℂ))
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hFd : Tendsto (fun t : ℝ => deriv F (t:ℂ)/F (t:ℂ)) atTop (𝓝 (a:ℂ)))
    (hHd : Tendsto (fun t : ℝ => deriv H (t:ℂ)/H (t:ℂ)) atTop (𝓝 (b:ℂ)))
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re) : a≤b := by
  by_contra hn
  have hba : b<a := lt_of_not_ge hn
  have ha : 0<a := hb.trans_lt hba
  obtain ⟨c,hbc,hca⟩ := exists_between hba
  let q := c/a
  have hq : q<1 := (div_lt_one ha).mpr hca
  have hqa : b<q*a := by dsimp [q]; rwa [div_mul_cancel₀ _ ha.ne']
  obtain ⟨C,hC,hbound⟩ := complex_log_derivative_power_bound hqa hHa hFa hHr hFr hHd hFd
  obtain ⟨D,hD,hO⟩ := hO
  have ht := (tendsto_rpow_atTop (show 0<1-q by linarith)).comp hFt
  obtain ⟨t,ht,hf,ho,hbnd⟩ := ((ht.eventually (eventually_gt_atTop (D*C))).and (hFr.and (hO.and hbound))).exists
  have hp : 0<((F (t:ℂ)).re)^q := Real.rpow_pos_of_pos hf.2 _
  have hh : (F (t:ℂ)).re≤(D*C)*((F (t:ℂ)).re)^q := by nlinarith
  have he : ((F (t:ℂ)).re)^(1-q)=(F (t:ℂ)).re/((F (t:ℂ)).re)^q := by
    rw [Real.rpow_sub hf.2,Real.rpow_one]
  dsimp only [Function.comp_apply] at ht
  rw [he] at ht
  exact (not_lt_of_ge ((div_le_iff₀ hp).mpr hh)) ht

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma norm_sub_real_part (z : ℂ) : ‖z-(z.re:ℂ)‖=|z.im| := by
  have he : z-(z.re:ℂ)=Complex.I*(z.im:ℂ) := by apply Complex.ext <;> simp
  rw [he,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]

theorem relative_strip_estimate {F : ℂ → ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,F z≠0)
    (hd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 0))
    {R : ℝ} (hR : 0<R) {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ,∀ z∈horizontalTail A R,
      F (z.re:ℂ)≠0 ∧ ‖F z/F (z.re:ℂ)-1‖≤ε*|z.im| := by
  let δ := min (ε/2) (1/(R+1))
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hb : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z ∧ F z≠0 ∧ ‖deriv F z/F z‖≤δ := by
    filter_upwards [ha,hz,(Metric.tendsto_nhds.mp hd) δ hδ] with z ha hz hd
    exact ⟨ha,hz,le_of_lt (by simpa only [dist_zero_right] using hd)⟩
  obtain ⟨A,hA⟩ := eventually_stripInfinity.mp hb R
  obtain ⟨L,hLa,hLe,hLd⟩ := analytic_log_on_convex (horizontalTail_open A R)
    (horizontalTail_convex A R)
    ⟨((A+1:ℝ):ℂ),⟨by simp,by simpa using hR⟩⟩
    (fun z hz => (hA z hz).1) (fun z hz => (hA z hz).2.1)
  refine ⟨A,?_⟩
  intro z hz
  have hzr : (z.re:ℂ)∈horizontalTail A R := ⟨hz.1,by simpa using hR⟩
  have hinc : ‖L z-L (z.re:ℂ)‖≤δ*|z.im| := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hLa z hz).differentiableAt)
      (fun z hz => by rw [hLd z hz]; exact (hA z hz).2.2)
      (horizontalTail_convex A R) hzr hz
    simpa only [norm_sub_real_part] using hh
  have hsmall : ‖L z-L (z.re:ℂ)‖≤1 := by
    apply hinc.trans
    have hδR : δ*(R+1)≤1 := by
      have hh := mul_le_mul_of_nonneg_right (min_le_right (ε/2) (1/(R+1))) (by positivity : 0≤R+1)
      simpa only [δ,one_div,inv_mul_cancel₀ (by positivity : R+1≠0)] using hh
    nlinarith [hz.2]
  have hratio : F z/F (z.re:ℂ)=Complex.exp (L z-L (z.re:ℂ)) := by
    rw [Complex.exp_sub,hLe z hz,hLe _ hzr]
  refine ⟨(hA _ hzr).2.1,?_⟩
  rw [hratio]
  calc
    ‖Complex.exp (L z-L (z.re:ℂ))-1‖ ≤ 2*‖L z-L (z.re:ℂ)‖ := Complex.norm_exp_sub_one_le hsmall
    _ ≤ 2*(δ*|z.im|) := mul_le_mul_of_nonneg_left hinc (by norm_num)
    _ ≤ ε*|z.im| := by
      have hh := mul_le_mul_of_nonneg_right (min_le_left (ε/2) (1/(R+1))) (abs_nonneg z.im)
      nlinarith

private lemma relative_strip_log_deriv_bound {function : ℂ → ℂ} {center : ℂ}
    {radius bound : ℝ} (hradius : 0<radius) (hbound : 0<bound)
    (hanalytic : AnalyticOnNhd ℂ function (ball center radius))
    (hnonzero : ∀ point∈ball center radius,function point≠0)
    (hlog : ∀ point∈ball center radius,|Real.log ‖function point‖|≤bound) :
    ‖deriv function center/function center‖≤8*bound/radius := by
  obtain ⟨logarithm,hlogarithm,hidentity,hderivative⟩ := analytic_log_on_convex
    isOpen_ball (convex_ball center radius) ⟨center,mem_ball_self hradius⟩ hanalytic hnonzero
  have hreal (point : ℂ) (hpoint : point∈ball center radius) :
      |(logarithm point).re|≤bound := by
    have hnorm := congrArg norm (hidentity point hpoint)
    rw [Complex.norm_exp] at hnorm
    have heq := congrArg Real.log hnorm
    rw [Real.log_exp] at heq
    rw [heq]
    exact hlog point hpoint
  let normalized : ℂ → ℂ := fun point => logarithm (center+point)-logarithm center
  have hmem {point : ℂ} (hpoint : point∈ball 0 radius) : center+point∈ball center radius := by
    simpa only [mem_ball_iff_norm,add_sub_cancel_left,sub_zero] using hpoint
  have hnormalized : AnalyticOnNhd ℂ normalized (ball 0 radius) := by
    intro point hpoint
    exact ((hlogarithm _ (hmem hpoint)).comp
      (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  have hreal_bound : MapsTo normalized (ball 0 radius) {point | point.re≤2*bound} := by
    intro point hpoint
    change (logarithm (center+point)).re-(logarithm center).re≤2*bound
    have hpoint_bound := abs_le.mp (hreal _ (hmem hpoint))
    have hcenter_bound := abs_le.mp (hreal _ (mem_ball_self hradius))
    linarith
  have hnorm_bound (point : ℂ) (hpoint : point∈sphere 0 (radius/2)) :
      ‖normalized point‖≤4*bound := by
    have hnorm : ‖point‖=radius/2 := by
      simpa only [mem_sphere_iff_norm,sub_zero] using hpoint
    have hinside : point∈ball 0 radius := by rw [mem_ball_zero_iff,hnorm]; linarith
    have hestimate := Complex.borelCaratheodory_zero (f := normalized)
      (by positivity : 0<2*bound) hnormalized.differentiableOn hreal_bound hradius hinside
      (by simp [normalized])
    rw [hnorm] at hestimate
    convert hestimate using 1
    field_simp
    ring
  have hclosure : closure (ball (0:ℂ) (radius/2)) ⊆ ball 0 radius := by
    rw [closure_ball _ (by positivity : radius/2≠0)]
    intro point hpoint
    rw [mem_ball_zero_iff]
    have hnorm : ‖point‖≤radius/2 := by
      simpa only [mem_closedBall_iff_norm,sub_zero] using hpoint
    linarith
  have hcontinuous : DiffContOnCl ℂ normalized (ball 0 (radius/2)) :=
    ((hnormalized.mono hclosure).differentiableOn).diffContOnCl
  have hestimate := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0<radius/2) hcontinuous hnorm_bound
  have hnormalized_deriv : deriv normalized 0=deriv logarithm center := by
    have hcenter : HasDerivAt logarithm (deriv logarithm center) (center+id (0:ℂ)) := by
      simpa using (hlogarithm center (mem_ball_self hradius)).differentiableAt.hasDerivAt
    have hcomposed := (hcenter.comp 0
      ((hasDerivAt_id (0:ℂ)).const_add center)).sub_const (logarithm center)
    simpa only [normalized,Function.comp_def,id_eq,mul_one] using hcomposed.deriv
  rw [hnormalized_deriv,hderivative _ (mem_ball_self hradius)] at hestimate
  convert hestimate using 1
  field_simp
  ring

private lemma relative_strip_log_deriv_tendsto {function : ℂ → ℂ}
    (hanalytic : ∀ᶠ point in sectorInfinity,AnalyticAt ℂ function point)
    (hnonzero : ∀ᶠ point in sectorInfinity,function point≠0)
    (hslow : SectorSlow function) (hinverse : SectorSlow (fun point => (function point)⁻¹)) :
    Tendsto (fun point => deriv function point/function point) stripInfinity (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let delta := epsilon/512
  have hdelta : 0<delta := by dsimp [delta]; positivity
  obtain ⟨upper,hupper,hupper_bound⟩ := (hslow delta hdelta).exists_pos
  obtain ⟨lower,hlower,hlower_bound⟩ := (hinverse delta hdelta).exists_pos
  have hbound : ∀ᶠ point in sectorInfinity,AnalyticAt ℂ function point ∧ function point≠0 ∧
      |Real.log ‖function point‖|≤|Real.log upper|+|Real.log lower|+delta*point.re := by
    filter_upwards [hanalytic,hnonzero,hupper_bound.bound,hlower_bound.bound]
      with point hanalytic hnonzero hupper_estimate hlower_estimate
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_inv]
      at hupper_estimate hlower_estimate
    have hnorm : 0<‖function point‖ := norm_pos_iff.mpr hnonzero
    have hupper_log := Real.log_le_log hnorm hupper_estimate
    have hlower_log := Real.log_le_log (inv_pos.mpr hnorm) hlower_estimate
    rw [Real.log_mul hupper.ne' (Real.exp_ne_zero _),Real.log_exp] at hupper_log
    rw [Real.log_mul hlower.ne' (Real.exp_ne_zero _),Real.log_exp,Real.log_inv] at hlower_log
    refine ⟨hanalytic,hnonzero,abs_le.mpr ⟨?_,?_⟩⟩
    · linarith [le_abs_self (Real.log lower),abs_nonneg (Real.log upper)]
    · linarith [le_abs_self (Real.log upper),abs_nonneg (Real.log lower)]
  obtain ⟨width,threshold,hwidth,hsector⟩ := hbound
  intro height
  obtain ⟨disc_threshold,hdiscs⟩ := eventually_atTop.mp (hwidth.real_discs threshold)
  let constant := |Real.log upper|+|Real.log lower|+1
  have hconstant : 0<constant := by dsimp [constant]; positivity
  let cutoff := max disc_threshold (max (8*|height|+1) (256*constant/epsilon))
  refine ⟨cutoff,?_⟩
  intro point hpoint
  have hthreshold : disc_threshold<point.re := (le_max_left _ _).trans_lt hpoint.1
  have hheight : 8*|height|+1<point.re :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hpoint.1
  have herror : 256*constant/epsilon<point.re :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hpoint.1
  have hpositive : 0<point.re := by linarith [abs_nonneg height]
  have himaginary : |point.im|<point.re/8 := by linarith [hpoint.2,le_abs_self height]
  have hdisc : ball point (point.re/8) ⊆ lossSector width threshold := by
    intro nearby hnearby
    apply (hdiscs point.re hthreshold.le).2
    rw [mem_closedBall_iff_norm]
    have hnorm : ‖point-(point.re:ℂ)‖=|point.im| := by
      have heq : point-(point.re:ℂ)=Complex.I*(point.im:ℂ) := by apply Complex.ext <;> simp
      rw [heq,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
    have hnearby_norm : ‖nearby-point‖<point.re/8 := mem_ball_iff_norm.mp hnearby
    calc
      ‖nearby-(point.re:ℂ)‖ = ‖(nearby-point)+(point-(point.re:ℂ))‖ := by congr 1; ring
      _ ≤ ‖nearby-point‖+‖point-(point.re:ℂ)‖ := norm_add_le _ _
      _ ≤ point.re/4 := by rw [hnorm]; linarith
  have hlog (nearby : ℂ) (hnearby : nearby∈ball point (point.re/8)) :
      |Real.log ‖function nearby‖|≤constant+2*delta*point.re := by
    have hreal := (le_abs_self (nearby-point).re).trans (Complex.abs_re_le_norm (nearby-point))
    simp only [Complex.sub_re] at hreal
    have hnorm : ‖nearby-point‖<point.re/8 := mem_ball_iff_norm.mp hnearby
    have hreal_bound : nearby.re≤2*point.re := by linarith
    have hlog_bound := (hsector nearby (hdisc hnearby)).2.2
    have hscaled := mul_le_mul_of_nonneg_left hreal_bound hdelta.le
    dsimp [constant]
    linarith
  have hderivative := relative_strip_log_deriv_bound (function := function) (center := point)
    (by positivity : 0<point.re/8) (by positivity : 0<constant+2*delta*point.re)
    (fun nearby hnearby => (hsector nearby (hdisc hnearby)).1)
    (fun nearby hnearby => (hsector nearby (hdisc hnearby)).2.1) hlog
  change dist (deriv function point/function point) 0<epsilon
  rw [dist_zero_right]
  apply hderivative.trans_lt
  rw [div_lt_iff₀ (by positivity : 0<point.re/8)]
  have hscaled_error := (div_lt_iff₀ hepsilon).mp herror
  dsimp [delta]
  nlinarith

lemma SectorSlow.relative_strip {F : ℂ → ℂ}
    (ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in sectorInfinity,F z≠0)
    (hf : SectorSlow F) (hi : SectorSlow (fun z => (F z)⁻¹))
    {R : ℝ} (hR : 0<R) {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ,∀ z∈horizontalTail A R,
      F (z.re:ℂ)≠0 ∧ ‖F z/F (z.re:ℂ)-1‖≤ε*|z.im| :=
  relative_strip_estimate (ha.filter_mono stripInfinity_le_sectorInfinity)
    (hz.filter_mono stripInfinity_le_sectorInfinity)
    (relative_strip_log_deriv_tendsto ha hz hf hi) hR hε

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem relative_strip_pair_estimate {F : ℂ → ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,F z≠0)
    (hd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 0))
    {R : ℝ} (hR : 0<R) {B : ℝ} (hB : 0<B) {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ,∀ z∈horizontalTail A R,∀ w∈horizontalTail A R,
      ‖z-w‖≤B → F w≠0 ∧ ‖F z/F w-1‖≤ε*‖z-w‖ := by
  let δ := min (ε/2) (1/(B+1))
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hb : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z ∧ F z≠0 ∧ ‖deriv F z/F z‖≤δ := by
    filter_upwards [ha,hz,(Metric.tendsto_nhds.mp hd) δ hδ] with z ha hz hd
    exact ⟨ha,hz,le_of_lt (by simpa only [dist_zero_right] using hd)⟩
  obtain ⟨A,hA⟩ := eventually_stripInfinity.mp hb R
  obtain ⟨L,hLa,hLe,hLd⟩ := analytic_log_on_convex (horizontalTail_open A R)
    (horizontalTail_convex A R)
    ⟨((A+1:ℝ):ℂ),⟨by simp,by simpa using hR⟩⟩
    (fun z hz => (hA z hz).1) (fun z hz => (hA z hz).2.1)
  refine ⟨A,?_⟩
  intro z hz w hzr hdist
  have hinc : ‖L z-L w‖≤δ*‖z-w‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hLa z hz).differentiableAt)
      (fun z hz => by rw [hLd z hz]; exact (hA z hz).2.2)
      (horizontalTail_convex A R) hzr hz
    exact hh
  have hsmall : ‖L z-L w‖≤1 := by
    apply hinc.trans
    have hδR : δ*(B+1)≤1 := by
      have hh := mul_le_mul_of_nonneg_right (min_le_right (ε/2) (1/(B+1))) (by positivity : 0≤B+1)
      simpa only [δ,one_div,inv_mul_cancel₀ (by positivity : B+1≠0)] using hh
    nlinarith
  have hratio : F z/F w=Complex.exp (L z-L w) := by
    rw [Complex.exp_sub,hLe z hz,hLe _ hzr]
  refine ⟨(hA _ hzr).2.1,?_⟩
  rw [hratio]
  calc
    ‖Complex.exp (L z-L w)-1‖ ≤ 2*‖L z-L w‖ := Complex.norm_exp_sub_one_le hsmall
    _ ≤ 2*(δ*‖z-w‖) := mul_le_mul_of_nonneg_left hinc (by norm_num)
    _ ≤ ε*‖z-w‖ := by
      have hh := mul_le_mul_of_nonneg_right (min_le_left (ε/2) (1/(B+1))) (norm_nonneg (z-w))
      nlinarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma exponential_normalized_log_deriv {F : ℂ → ℂ} {a : ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,F z≠0)
    (hd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 a)) :
    Tendsto (fun z => deriv (fun w => Complex.exp (-a*w)*F w) z /
      (Complex.exp (-a*z)*F z)) stripInfinity (𝓝 0) := by
  have hh := hd.sub_const a
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [ha,hz] with z ha hz
  have hde := ((Complex.hasDerivAt_exp (-a*z)).comp z ((hasDerivAt_id z).const_mul (-a))).mul ha.differentiableAt.hasDerivAt
  change HasDerivAt (fun w => Complex.exp (-a*w)*F w) _ z at hde
  change deriv F z/F z-a=deriv (fun w => Complex.exp (-a*w)*F w) z/(Complex.exp (-a*z)*F z)
  rw [hde.deriv]
  simp only [Function.comp_apply,mul_one]
  field_simp [hz,Complex.exp_ne_zero]
  ring

theorem affine_relative_strip_pair_estimate {F : ℂ → ℂ} {a : ℂ}
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,F z≠0)
    (hd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 a))
    {R : ℝ} (hR : 0<R) {B : ℝ} (hB : 0<B) {ε : ℝ} (hε : 0<ε) :
    ∃ A : ℝ,∀ z∈horizontalTail A R,∀ w∈horizontalTail A R,
      ‖z-w‖≤B → F w≠0 ∧
        ‖Complex.exp (-a*(z-w))*(F z/F w)-1‖≤ε*‖z-w‖ := by
  let G : ℂ → ℂ := fun z => Complex.exp (-a*z)*F z
  have hGa : ∀ᶠ z in stripInfinity,AnalyticAt ℂ G z :=
    ha.mono (fun z hz => ((analyticAt_const.mul analyticAt_id).cexp).mul hz)
  have hG0 : ∀ᶠ z in stripInfinity,G z≠0 := hz.mono (fun z hz => mul_ne_zero (Complex.exp_ne_zero _) hz)
  obtain ⟨A,hA⟩ := relative_strip_pair_estimate hGa hG0
    (exponential_normalized_log_deriv ha hz hd) hR hB hε
  refine ⟨A,?_⟩
  intro z hz w hw hdzw
  obtain ⟨hne,hbound⟩ := hA z hz w hw hdzw
  have hFw : F w≠0 := fun he => hne (by simp [G,he])
  refine ⟨hFw,?_⟩
  have he : G z/G w=Complex.exp (-a*(z-w))*(F z/F w) := by
    dsimp [G]
    rw [show -a*(z-w)=(-a*z)-(-a*w) by ring,Complex.exp_sub]
    ring
  rwa [he] at hbound

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
namespace DegeneratingTrees.Clock

lemma inverse_increment_error_tendsto {x : ℂ → ℂ} {b : ℝ}
    (hi : ∀ ε : ℝ,0<ε → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤ε*|w.arg|) :
    Tendsto (fun w => x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)) sectorInfinity (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hi (ε/(Real.pi+1)) (by positivity)] with w hw
  rw [dist_zero_right]
  have hh := mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi w) (by positivity : 0≤ε/(Real.pi+1))
  apply (hw.trans hh).trans_lt
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ (by positivity : 0<Real.pi+1)).mpr (by nlinarith [Real.pi_pos])

lemma inverse_pair_bounded {x : ℂ → ℂ} {b : ℝ} (hb : 0<b)
    (hr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (hi : ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤|w.arg|) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)‖≤B ∧ |(x w).im|≤B ∧ (x (‖w‖:ℂ)).im=0 := by
  let B := Real.pi+Real.pi/b+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [hi,tendsto_norm_sectorInfinity.eventually hr] with w hw hr
  have hd : ‖x w-x (‖w‖:ℂ)‖≤B := by
    have hnorm : ‖Complex.I*(w.arg/b:ℝ)‖=|w.arg|/b := by
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hb]
    calc
      ‖x w-x (‖w‖:ℂ)‖ ≤ ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖+‖Complex.I*(w.arg/b:ℝ)‖ := norm_le_norm_sub_add _ _
      _ ≤ |w.arg|+|w.arg|/b := by rw [hnorm]; exact add_le_add hw le_rfl
      _ ≤ B := by
        have hp := Complex.abs_arg_le_pi w
        have hp' := div_le_div_of_nonneg_right hp hb.le
        dsimp [B]
        linarith
  refine ⟨hd,?_,hr⟩
  have hh := (Complex.abs_im_le_norm (x w-x (‖w‖:ℂ))).trans hd
  simpa only [Complex.sub_im,hr,sub_zero] using hh

theorem inverse_clock_ratio_tendsto {F x : ℂ → ℂ} {a : ℂ} {b : ℝ} (hb : 0<b)
    (ha : ∀ᶠ z in stripInfinity,AnalyticAt ℂ F z)
    (hz : ∀ᶠ z in stripInfinity,F z≠0)
    (hd : Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 a))
    (hx : Tendsto (fun w => (x w).re) sectorInfinity atTop)
    (ht : Tendsto (fun r : ℝ => (x (r:ℂ)).re) atTop atTop)
    (hr : ∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0)
    (hi : ∀ ε : ℝ,0<ε → ∀ᶠ w in sectorInfinity,
      ‖x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ)‖≤ε*|w.arg|) :
    Tendsto (fun w => Complex.exp (-a*Complex.I*(w.arg/b:ℝ)) *
      (F (x w)/F (x (‖w‖:ℂ)))) sectorInfinity (𝓝 1) := by
  obtain ⟨B,hB,hbound⟩ := inverse_pair_bounded hb hr (by simpa only [one_mul] using hi 1 zero_lt_one)
  have hpair : Tendsto (fun w => Complex.exp (-a*(x w-x (‖w‖:ℂ)))*
      (F (x w)/F (x (‖w‖:ℂ)))) sectorInfinity (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨A,hA⟩ := affine_relative_strip_pair_estimate ha hz hd
      (show 0<B+1 by linarith) hB (show 0<ε/(B+1) by positivity)
    filter_upwards [hbound,hx.eventually (eventually_gt_atTop A),
      (ht.comp tendsto_norm_sectorInfinity).eventually (eventually_gt_atTop A)] with w hbw hx ht
    have hw : x w∈horizontalTail A (B+1) := ⟨hx,by linarith [hbw.2.1]⟩
    have hwr : x (‖w‖:ℂ)∈horizontalTail A (B+1) := ⟨ht,by rw [hbw.2.2,abs_zero]; linarith⟩
    have hh := (hA _ hw _ hwr hbw.1).2
    rw [dist_eq_norm]
    apply (hh.trans (mul_le_mul_of_nonneg_left hbw.1 (by positivity))).trans_lt
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by linarith : 0<B+1)).mpr (by nlinarith)
  have herror := inverse_increment_error_tendsto hi
  have hmul := (tendsto_const_nhds (x := a)).mul herror
  simp only [mul_zero] at hmul
  have hexp := (Complex.continuous_exp.tendsto 0).comp hmul
  simp only [Complex.exp_zero] at hexp
  have hh := hexp.mul hpair
  simp only [one_mul] at hh
  apply hh.congr'
  exact Eventually.of_forall fun w => by
    change Complex.exp (a*(x w-x (‖w‖:ℂ)-Complex.I*(w.arg/b:ℝ))) *
      (Complex.exp (-a*(x w-x (‖w‖:ℂ)))*(F (x w)/F (x (‖w‖:ℂ)))) = _
    rw [←mul_assoc,←Complex.exp_add]
    congr 2
    ring

lemma inverse_clock_modulus_tendsto {F x : ℂ → ℂ} {a b : ℝ}
    (h : Tendsto (fun w => Complex.exp (-(a:ℂ)*Complex.I*(w.arg/b:ℝ)) *
      (F (x w)/F (x (‖w‖:ℂ)))) sectorInfinity (𝓝 1)) :
    Tendsto (fun w => ‖F (x w)‖/‖F (x (‖w‖:ℂ))‖) sectorInfinity (𝓝 1) := by
  have hh := h.norm
  simp only [norm_one] at hh
  apply hh.congr'
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [norm_mul,norm_div,Complex.norm_exp]
    have he : (-(a:ℂ)*Complex.I*(w.arg/b:ℝ)).re=0 := by simp
    rw [he,Real.exp_zero,one_mul]

end DegeneratingTrees.Clock
end

end OAI
