import OAI.Analysis.NodalLength.Decomposition

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma fderiv_log_norm_apply {x : Plane} (hx : x≠0) (v : Plane) :
    (fderiv ℝ (fun y : Plane => Real.log ‖y‖) x) v=inner ℝ x v/‖x‖^2 := by
  have hd := (((hasFDerivAt_id (𝕜:=ℝ) x).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).const_mul (1/2:ℝ)
  have heq : (fun y : Plane => Real.log ‖y‖)=(fun y : Plane => (1/2:ℝ)*Real.log (‖y‖^2)) := by
    funext y
    rw [Real.log_pow]
    ring
  dsimp only [id_eq] at hd
  rw [heq,hd.fderiv]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply]
  ring

lemma fderiv_smoothLog_unit {w : Plane} (hw : ‖w‖=1) (v : Plane) :
    (fderiv ℝ parametrixSmoothLog w) v=inner ℝ w v := by
  have he : parametrixSmoothLog =ᶠ[𝓝 w] (fun y : Plane => Real.log ‖y‖) := by
    have hn : {y : Plane | (1/8:ℝ)<‖y‖}∈𝓝 w :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds (by norm_num [hw])
    filter_upwards [hn] with y hy
    exact parametrixSmoothLog_eq hy.le
  rw [he.fderiv_eq,fderiv_log_norm_apply (by intro h; simp [h] at hw),hw]
  norm_num

lemma smoothLog_hessian_bounded : ∃C : ℝ,0≤C ∧ ∀x∈Metric.closedBall (0:Plane) 2,
    ∀i j : Fin 2,|coordPartial (coordPartial parametrixSmoothLog i) j x|≤C := by
  let g : Plane → ℝ := fun x => ∑i : Fin 2,∑j : Fin 2,|coordPartial (coordPartial parametrixSmoothLog i) j x|
  have hg : Continuous g := continuous_finsetSum _ (fun i _ =>
    continuous_finsetSum _ (fun j _ => (smooth_partial (smooth_partial smooth_parametrixSmoothLog i) j).continuous.abs))
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Plane) 2).bddAbove_image hg.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x hx i j
  have h1 : |coordPartial (coordPartial parametrixSmoothLog i) j x|≤g x := by
    apply le_trans (Finset.single_le_sum (fun k _ => abs_nonneg (coordPartial (coordPartial parametrixSmoothLog i) k x)) (Finset.mem_univ j))
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (coordPartial (coordPartial parametrixSmoothLog k) l x))) (Finset.mem_univ i)
  exact h1.trans ((hB (mem_image_of_mem _ hx)).trans (le_max_left _ _))

lemma normalized_log_affine_error : ∃C : ℝ,0≤C ∧ ∀w v : Plane,‖w‖=1 → ‖v‖≤1/2 →
    |Real.log ‖w+v‖-inner ℝ w v|≤C*‖v‖^2 := by
  obtain ⟨C,hC,hess⟩ := smoothLog_hessian_bounded
  refine ⟨4*C,by positivity,?_⟩
  intro w v hw hv
  have hball : Metric.closedBall w ‖v‖⊆Metric.closedBall (0:Plane) 2 := by
    intro x hx
    have hn : ‖x-w‖≤‖v‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have ht := norm_add_le (x-w) w
    simp only [sub_add_cancel,hw] at ht
    simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖x‖≤2 by linarith)
  have hnorm : (1/8:ℝ)≤‖w+v‖ := by
    have ht := norm_add_le (w+v) (-v)
    simp only [add_neg_cancel_right,norm_neg,hw] at ht
    linarith
  have hh := affine_error_bound_ball smooth_parametrixSmoothLog (norm_nonneg v) hC
    (fun x hx => hess x (hball hx)) (show w+v∈Metric.closedBall w ‖v‖ by simp [dist_eq_norm])
  rw [parametrixSmoothLog_eq hnorm,parametrixSmoothLog_eq (by norm_num [hw]),hw,Real.log_one,sub_zero,
    add_sub_cancel_left,fderiv_smoothLog_unit hw] at hh
  exact hh

lemma log_far_affine_error : ∃C : ℝ,0≤C ∧ ∀x y z : Plane,∀r : ℝ,0≤r →
    ‖x-y‖≤r → 2*r<‖y-z‖ →
    |Real.log ‖x-z‖-Real.log ‖y-z‖-inner ℝ (y-z) (x-y)/‖y-z‖^2|≤C*r^2/‖y-z‖^2 := by
  obtain ⟨C,hC,herr⟩ := normalized_log_affine_error
  refine ⟨C,hC,?_⟩
  intro x y z r hr hxy hfar
  let d := ‖y-z‖
  have hd : 0<d := lt_of_le_of_lt (by positivity) hfar
  let w : Plane := d⁻¹ • (y-z)
  let v : Plane := d⁻¹ • (x-y)
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]; exact inv_mul_cancel₀ hd.ne'
  have hvnorm : ‖v‖=‖x-y‖/d := by simp only [v,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),div_eq_mul_inv,mul_comm]
  have hv : ‖v‖≤1/2 := by rw [hvnorm,div_le_iff₀ hd]; dsimp [d]; linarith
  have hh := herr w v hw hv
  have hwv : w+v=d⁻¹ • (x-z) := by dsimp [w,v]; rw [← smul_add]; congr 1; abel
  have hxz : x-z≠0 := by
    intro he
    have he' : x=z := sub_eq_zero.mp he
    subst x
    rw [norm_sub_rev] at hxy
    linarith
  have hlog : Real.log ‖w+v‖=Real.log ‖x-z‖-Real.log d := by
    rw [hwv,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),Real.log_mul (inv_ne_zero hd.ne') (norm_ne_zero_iff.mpr hxz),Real.log_inv]
    ring
  have hinner : inner ℝ w v=inner ℝ (y-z) (x-y)/d^2 := by simp only [w,v,inner_smul_left,inner_smul_right,conj_trivial]; ring
  rw [hlog,hinner] at hh
  apply hh.trans
  rw [hvnorm]
  dsimp only [d]
  have hs : ‖x-y‖^2≤r^2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
  exact (le_of_eq (by ring)).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (sq_nonneg _))

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma volume_unit_disk_real : volume.real (Metric.ball (0:Plane) 1)=Real.pi := by
  simp [measureReal_def,EuclideanSpace.volume_ball_fin_two,ENNReal.toReal_ofReal Real.pi_pos.le]

lemma log_scaled_kernel_ae {ρ : ℝ} (hρ : 0<ρ) (y z : Plane) :
    ∀ᵐξ : Plane, Real.log ‖y+ρ • ξ-z‖=Real.log ρ+Real.log ‖ξ-ρ⁻¹ • (z-y)‖ := by
  filter_upwards [Measure.ae_ne volume (ρ⁻¹ • (z-y))] with ξ hξ
  have he : y+ρ • ξ-z=ρ • (ξ-ρ⁻¹ • (z-y)) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hρ.ne',one_smul]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hρ,Real.log_mul hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hξ))]

lemma log_scaled_kernel_integrable {ρ : ℝ} (hρ : 0<ρ) (y z : Plane) :
    IntegrableOn (fun ξ : Plane => Real.log ‖y+ρ • ξ-z‖) (Metric.ball 0 1) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩
  have ht : ‖ρ⁻¹ • (z-y)‖<‖ρ⁻¹ • (z-y)‖+1 := by linarith
  exact ((integrable_const (Real.log ρ)).add (log_translate_local (R:=1) ht).1).congr
    (Filter.EventuallyEq.symm (ae_restrict_of_ae (log_scaled_kernel_ae hρ y z)))

def logDiskAverage (y : Plane) (ρ : ℝ) (z : Plane) : ℝ :=
  Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖y+ρ • ξ-z‖)

lemma logDiskAverage_scale {ρ : ℝ} (hρ : 0<ρ) (y z : Plane) :
    logDiskAverage y ρ z=Real.log ρ+Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖ξ-ρ⁻¹ • (z-y)‖) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩
  have ht : ‖ρ⁻¹ • (z-y)‖<‖ρ⁻¹ • (z-y)‖+1 := by linarith
  rw [logDiskAverage,integral_congr_ae (ae_restrict_of_ae (log_scaled_kernel_ae hρ y z)),
    integral_add (integrable_const _) (log_translate_local (R:=1) ht).1,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change Real.pi⁻¹*(volume.real (Metric.ball (0:Plane) 1)*Real.log ρ+_)=_
  rw [volume_unit_disk_real]
  field_simp

lemma log_near_average_lower {R : ℝ} (_hR : 0≤R) : ∃B : ℝ,0≤B ∧ ∀y z : Plane,∀ρ : ℝ,
    0<ρ → ‖z-y‖≤2*R*ρ → Real.log ρ-B≤logDiskAverage y ρ z := by
  let L := ∫ξ in Metric.ball (0:Plane) (2*R+2),‖Real.log ‖ξ‖‖
  refine ⟨Real.pi⁻¹*L,by positivity,?_⟩
  intro y z ρ hρ hnear
  have ht : ‖ρ⁻¹ • (z-y)‖<2*R+1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
    have hle : ρ⁻¹*‖z-y‖≤2*R := by
      calc _ ≤ ρ⁻¹*(2*R*ρ) := mul_le_mul_of_nonneg_left hnear (inv_nonneg.mpr hρ.le)
           _ = _ := by field_simp
    linarith
  have hl : -(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖ξ-ρ⁻¹ • (z-y)‖)≤L := by
    calc
      _ ≤ |∫ξ in Metric.ball (0:Plane) 1,Real.log ‖ξ-ρ⁻¹ • (z-y)‖| := neg_le_abs _
      _ ≤ ∫ξ in Metric.ball (0:Plane) 1,‖Real.log ‖ξ-ρ⁻¹ • (z-y)‖‖ := by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun ξ : Plane => Real.log ‖ξ-ρ⁻¹ • (z-y)‖) (μ:=volume.restrict (Metric.ball (0:Plane) 1)))
      _ ≤ L := by simpa only [show (1+(2*R+1):ℝ)=2*R+2 by ring] using (log_translate_local (R:=1) ht).2
  rw [logDiskAverage_scale hρ]
  nlinarith [mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr Real.pi_pos.le)]

lemma log_near_outer_upper {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) {x y z : Plane}
    (hx : ‖x-y‖≤R*ρ) (hz : ‖z-y‖≤2*R*ρ) (hxz : x≠z) :
    Real.log ‖x-z‖≤Real.log ρ+Real.log (3*R) := by
  have hn : ‖x-z‖≤ρ*(3*R) := by
    have htri := norm_sub_le (x-y) (z-y)
    rw [sub_sub_sub_cancel_right] at htri
    nlinarith
  have hh := Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hxz)) hn
  rwa [Real.log_mul hρ.ne' (by positivity : (3*R:ℝ)≠0)] at hh

lemma integral_linear_unitDisk (L : Plane →L[ℝ] ℝ) :
    (∫ξ in Metric.ball (0:Plane) 1,L ξ)=0 := by
  let f := (Metric.ball (0:Plane) 1).indicator (fun ξ => L ξ)
  have he : (fun ξ => f (-ξ))=(fun ξ => -f ξ) := by
    funext ξ
    by_cases hξ : ξ∈Metric.ball (0:Plane) 1
    · have hneg : -ξ∈Metric.ball (0:Plane) 1 := by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hξ
      simp only [f,indicator_of_mem hξ,indicator_of_mem hneg,map_neg]
    · have hneg : -ξ∉Metric.ball (0:Plane) 1 := by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hξ
      simp only [f,indicator_of_notMem hξ,indicator_of_notMem hneg,neg_zero]
  have hh := integral_neg_eq_self f volume
  rw [he,integral_neg] at hh
  rw [← integral_indicator measurableSet_ball]
  change (∫ξ,f ξ)=0
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma log_far_diskAverage_error : ∃C : ℝ,0≤C ∧ ∀y z : Plane,∀ρ : ℝ,0<ρ →
    2*ρ<‖y-z‖ → |logDiskAverage y ρ z-Real.log ‖y-z‖|≤C*ρ^2/‖y-z‖^2 := by
  obtain ⟨C,hC,herr⟩ := log_far_affine_error
  refine ⟨C,hC,?_⟩
  intro y z ρ hρ hfar
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩
  let L : Plane →L[ℝ] ℝ := (‖y-z‖^2)⁻¹ • (ρ • innerSL ℝ (y-z))
  have hL (ξ : Plane) : L ξ=inner ℝ (y-z) (ρ • ξ)/‖y-z‖^2 := by
    simp only [L,smul_apply,innerSL_apply_apply,smul_eq_mul,inner_smul_right]; ring
  let F : Plane → ℝ := fun ξ => Real.log ‖y+ρ • ξ-z‖-Real.log ‖y-z‖-L ξ
  have hiL : IntegrableOn (fun ξ => L ξ) (Metric.ball (0:Plane) 1) :=
    (L.continuous.continuousOn.integrableOn_compact (isCompact_closedBall (0:Plane) 1)).mono_set Metric.ball_subset_closedBall
  have hi := log_scaled_kernel_integrable hρ y z
  have hbound : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),‖F ξ‖≤C*ρ^2/‖y-z‖^2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with ξ hξ
    have hnorm : ‖y+ρ • ξ-y‖≤ρ := by
      simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
      have hx : ‖ξ‖≤1 := (show ‖ξ‖<1 by simpa only [Metric.mem_ball,dist_zero_right] using hξ).le
      nlinarith
    simpa only [F,Real.norm_eq_abs,add_sub_cancel_left,← hL] using herr (y+ρ • ξ) y z ρ hρ.le hnorm hfar
  have hh := norm_integral_le_of_norm_le_const hbound
  have hint : (∫ξ in Metric.ball (0:Plane) 1,F ξ)=Real.pi*(logDiskAverage y ρ z-Real.log ‖y-z‖) := by
    rw [show F=(fun ξ => (Real.log ‖y+ρ • ξ-z‖-Real.log ‖y-z‖)-L ξ) from rfl,
      integral_sub (f:=fun ξ => Real.log ‖y+ρ • ξ-z‖-Real.log ‖y-z‖) (g:=fun ξ => L ξ) (hi.sub (integrable_const (Real.log ‖y-z‖))) hiL,integral_sub hi (integrable_const (Real.log ‖y-z‖)),
      integral_linear_unitDisk,sub_zero,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
    change (∫ξ in Metric.ball (0:Plane) 1,Real.log ‖y+ρ • ξ-z‖)-volume.real (Metric.ball (0:Plane) 1)*Real.log ‖y-z‖=_
    rw [volume_unit_disk_real,logDiskAverage]
    field_simp
  rw [hint,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] at hh
  have hvol : (volume.restrict (Metric.ball (0:Plane) 1)).real univ=Real.pi := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using volume_unit_disk_real
  rw [hvol] at hh
  nlinarith [Real.pi_pos]

lemma logarithmic_kernel_comparison {R : ℝ} (hR : 1≤R) :
    ∃C : ℝ,0≤C ∧ ∀x y z : Plane,∀ρ : ℝ,0<ρ → ‖x-y‖≤R*ρ → x≠z →
    Real.log ‖x-z‖-logDiskAverage y ρ z-
      (if 2*R*ρ<‖y-z‖ then inner ℝ (y-z) (x-y)/‖y-z‖^2 else 0)
      ≤ C*(if 2*R*ρ<‖y-z‖ then ρ^2/‖y-z‖^2 else 1) := by
  obtain ⟨Cf,hCf,hfar⟩ := log_far_affine_error
  obtain ⟨Ca,hCa,hav⟩ := log_far_diskAverage_error
  obtain ⟨B,hB,hnear⟩ := log_near_average_lower (show 0≤R by linarith)
  let C := Cf*R^2+Ca+|Real.log (3*R)|+B
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x y z ρ hρ hx hxz
  split_ifs with hz
  · have hfar1 : 2*ρ<‖y-z‖ := by nlinarith
    have ho := (le_abs_self _).trans (hfar x y z (R*ρ) (by positivity) hx (by nlinarith))
    have hi := (neg_le_abs _).trans (hav y z ρ hρ hfar1)
    have hnon : 0≤ρ^2/‖y-z‖^2 := by positivity
    have hCle : Cf*R^2+Ca≤C := by dsimp [C]; linarith [abs_nonneg (Real.log (3*R))]
    have hc := mul_le_mul_of_nonneg_right hCle hnon
    nlinarith [show Cf*(R*ρ)^2/‖y-z‖^2+Ca*ρ^2/‖y-z‖^2=(Cf*R^2+Ca)*(ρ^2/‖y-z‖^2) by ring]
  · have hn : ‖z-y‖≤2*R*ρ := by rw [norm_sub_rev]; exact le_of_not_gt hz
    have ho := log_near_outer_upper (show 0<R by linarith) hρ hx hn hxz
    have hi := hnear y z ρ hρ hn
    have hlog := le_abs_self (Real.log (3*R))
    have hpos : 0≤Cf*R^2+Ca := by positivity
    dsimp [C]
    linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

instance unitDisk_volume_finite : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩

lemma scaled_log_kernel_norm_bound {ρ S : ℝ} (hρ : 0<ρ) (y z : Plane)
    (hS : ‖ρ⁻¹ • (z-y)‖<S) :
    (∫ξ in Metric.ball (0:Plane) 1,‖Real.log ‖y+ρ • ξ-z‖‖)≤
      Real.pi*|Real.log ρ|+(∫ξ in Metric.ball (0:Plane) (1+S),‖Real.log ‖ξ‖‖) := by
  have hi := (log_scaled_kernel_integrable hρ y z).norm
  have ht := (log_translate_local (R:=1) hS).1.norm
  have hle : (∫ξ in Metric.ball (0:Plane) 1,‖Real.log ‖y+ρ • ξ-z‖‖)≤
      ∫ξ in Metric.ball (0:Plane) 1,(|Real.log ρ|+‖Real.log ‖ξ-ρ⁻¹ • (z-y)‖‖) := by
    apply integral_mono_ae hi ((integrable_const _).add ht)
    filter_upwards [ae_restrict_of_ae (log_scaled_kernel_ae hρ y z)] with ξ hξ
    rw [hξ]
    simpa only [Real.norm_eq_abs,Pi.add_apply] using norm_add_le (Real.log ρ) (Real.log ‖ξ-ρ⁻¹ • (z-y)‖)
  rw [integral_add (integrable_const _) ht,integral_const] at hle
  have hvol : (volume.restrict (Metric.ball (0:Plane) 1)).real univ=Real.pi := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using volume_unit_disk_real
  rw [hvol,smul_eq_mul] at hle
  exact hle.trans (add_le_add le_rfl (log_translate_local (R:=1) hS).2)

lemma scaled_logPotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    Integrable (fun p : Plane×Plane => Real.log ‖y+ρ • p.1-p.2‖)
      ((volume.restrict (Metric.ball 0 1)).prod ν) := by
  have hm : Measurable (fun p : Plane×Plane => Real.log ‖y+ρ • p.1-p.2‖) :=
    Real.measurable_log.comp ((measurable_const.add (measurable_fst.const_smul ρ)).sub measurable_snd).norm
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun z => log_scaled_kernel_integrable hρ y z),?_⟩
  let S := ρ⁻¹*(4+‖y‖)+1
  apply (integrable_const (Real.pi*|Real.log ρ|+(∫ξ in Metric.ball (0:Plane) (1+S),‖Real.log ‖ξ‖‖))).mono'
    hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [hs] with z hz
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  apply scaled_log_kernel_norm_bound hρ y z
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
  have htri := norm_sub_le z y
  have hmul := mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr hρ.le)
  dsimp [S]
  nlinarith [inv_pos.mpr hρ]

lemma scaled_aeLogPotential_integrableOn (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    IntegrableOn (fun ξ : Plane => aeLogPotential ν (y+ρ • ξ)) (Metric.ball 0 1) :=
  (scaled_logPotential_prod_integrable ν hs hρ y).integral_prod_left

lemma logDiskAverage_integrable (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    Integrable (logDiskAverage y ρ) ν :=
  (scaled_logPotential_prod_integrable ν hs hρ y).integral_prod_right.const_mul Real.pi⁻¹

lemma integral_logDiskAverage (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    (∫z,logDiskAverage y ρ z ∂ν)=Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,aeLogPotential ν (y+ρ • ξ)) := by
  rw [show logDiskAverage y ρ=(fun z => Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖y+ρ • ξ-z‖)) from rfl,integral_const_mul]
  have hi : Integrable (Function.uncurry (fun z ξ : Plane => Real.log ‖y+ρ • ξ-z‖))
      (ν.prod (volume.restrict (Metric.ball 0 1))) := by
    simpa only [Function.uncurry_def,Function.comp_def,Prod.fst_swap,Prod.snd_swap] using (scaled_logPotential_prod_integrable ν hs hρ y).swap
  rw [integral_integral_swap hi]
  rfl

lemma ae_source_ne (ν : Measure Plane) [IsFiniteMeasure ν] : ∀ᵐx : Plane,∀ᵐz ∂ν,x≠z := by
  apply (Measure.ae_ae_comm (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Eventually.of_forall (fun z => Measure.ae_ne volume z)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def farGradient (R ρ : ℝ) (y z : Plane) : Plane :=
  if 2*R*ρ<‖y-z‖ then (‖y-z‖^2)⁻¹ • (y-z) else 0

def farWeight (R ρ : ℝ) (y z : Plane) : ℝ :=
  if 2*R*ρ<‖y-z‖ then ρ^2/‖y-z‖^2 else 1

lemma measurable_farGradient (R ρ : ℝ) (y : Plane) : Measurable (farGradient R ρ y) := by
  exact Measurable.ite (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).measurableSet
    ((((measurable_const.sub measurable_id).norm.pow_const 2).inv).smul (measurable_const.sub measurable_id)) measurable_const

lemma measurable_farWeight (R ρ : ℝ) (y : Plane) : Measurable (farWeight R ρ y) := by
  exact Measurable.ite (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).measurableSet
    (measurable_const.div ((measurable_const.sub measurable_id).norm.pow_const 2)) measurable_const

lemma farGradient_inner (R ρ : ℝ) (y z v : Plane) :
    inner ℝ (farGradient R ρ y z) v=
      if 2*R*ρ<‖y-z‖ then inner ℝ (y-z) v/‖y-z‖^2 else 0 := by
  unfold farGradient
  split_ifs <;> simp only [inner_smul_left,conj_trivial,inner_zero_left]
  ring

lemma farGradient_norm_bound {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) (y z : Plane) :
    ‖farGradient R ρ y z‖≤(2*R*ρ)⁻¹ := by
  unfold farGradient
  split_ifs with hz
  · have hd : 0<‖y-z‖ := lt_trans (by positivity : 0<2*R*ρ) hz
    have he : ‖(‖y-z‖^2)⁻¹ • (y-z)‖=‖y-z‖⁻¹ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(‖y-z‖^2)⁻¹)]
      field_simp
    rw [he]
    exact (inv_le_inv₀ hd (show 0<2*R*ρ by positivity)).mpr hz.le
  · simp only [norm_zero]
    positivity

lemma farWeight_bounds {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (y z : Plane) :
    0≤farWeight R ρ y z ∧ farWeight R ρ y z≤1 := by
  unfold farWeight
  split_ifs with hz
  · have hd : 0<‖y-z‖ := by nlinarith
    refine ⟨by positivity,?_⟩
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    have hsmall : ρ≤‖y-z‖ := by nlinarith
    nlinarith [sq_nonneg (‖y-z‖-ρ)]
  · exact ⟨by norm_num,le_rfl⟩

lemma integrable_farGradient (ν : Measure Plane) [IsFiniteMeasure ν]
    {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) (y : Plane) : Integrable (farGradient R ρ y) ν :=
  (integrable_const ((2*R*ρ)⁻¹)).mono' (measurable_farGradient R ρ y).aestronglyMeasurable
    (Eventually.of_forall (farGradient_norm_bound hR hρ y))

lemma integrable_farWeight (ν : Measure Plane) [IsFiniteMeasure ν]
    {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (y : Plane) : Integrable (farWeight R ρ y) ν := by
  apply (integrable_const (1:ℝ)).mono' (measurable_farWeight R ρ y).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (farWeight_bounds hR hρ y z).1]
  exact (farWeight_bounds hR hρ y z).2

lemma integral_inner_left {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → Plane} (hf : Integrable f ν) (v : Plane) :
    (∫z,inner ℝ (f z) v ∂ν)=inner ℝ (∫z,f z ∂ν) v := by
  simp_rw [real_inner_comm]
  exact integral_inner hf v

lemma ae_potential_affine_comparison {R : ℝ} (hR : 1≤R) : ∃C : ℝ,0≤C ∧
    ∀ν : Measure Plane,∀[IsFiniteMeasure ν], (∀ᵐz ∂ν,‖z‖<4) →
    ∀ρ : ℝ,0<ρ → ∀y : Plane,
    ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 3), ‖x-y‖≤R*ρ →
    aeLogPotential ν x-(∫z,logDiskAverage y ρ z ∂ν)-
      inner ℝ (∫z,farGradient R ρ y z ∂ν) (x-y)≤C*(∫z,farWeight R ρ y z ∂ν) := by
  obtain ⟨C,hC,hkernel⟩ := logarithmic_kernel_comparison hR
  refine ⟨C,hC,?_⟩
  intro ν _ hs ρ hρ y
  have hg := integrable_farGradient ν (show 0<R by linarith) hρ y
  have hw := integrable_farWeight ν hR hρ y
  have ha := logDiskAverage_integrable ν hs hρ y
  filter_upwards [(logPotential_prod_integrable ν hs 3).prod_right_ae,
    ae_restrict_of_ae (ae_source_ne ν)] with x hx hne hxy
  have hi := (hx.sub ha).sub (hg.inner_const (x-y))
  have hh : (∫z,(Real.log ‖x-z‖-logDiskAverage y ρ z-inner ℝ (farGradient R ρ y z) (x-y)) ∂ν)≤
      ∫z,C*farWeight R ρ y z ∂ν := by
    apply integral_mono_ae hi (hw.const_mul C)
    filter_upwards [hne] with z hz
    simpa only [Pi.sub_apply,Pi.mul_apply,farGradient_inner,farWeight] using hkernel x y z ρ hρ hxy hz
  rw [integral_sub (f:=fun z => Real.log ‖x-z‖-logDiskAverage y ρ z) (g:=fun z => inner ℝ (farGradient R ρ y z) (x-y)) (hx.sub ha) (hg.inner_const (x-y)),
    integral_sub hx ha,integral_const_mul,integral_inner_left hg] at hh
  exact hh

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def diskAverage (f : Plane → ℝ) (y : Plane) (ρ : ℝ) : ℝ :=
  Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,f (y+ρ • ξ))

lemma scaled_continuous_integrable {f : Plane → ℝ} (hf : Continuous f) (y : Plane) (ρ : ℝ) :
    IntegrableOn (fun ξ : Plane => f (y+ρ • ξ)) (Metric.ball 0 1) :=
  ((hf.comp (continuous_const.add (continuous_const_smul ρ))).continuousOn.integrableOn_compact
    (isCompact_closedBall (0:Plane) 1)).mono_set Metric.ball_subset_closedBall

lemma diskAverage_linear (L : Plane →L[ℝ] ℝ) (y : Plane) (ρ : ℝ) :
    diskAverage (fun x => L (x-y)) y ρ=0 := by
  have he : (fun ξ : Plane => L (y+ρ • ξ-y))=(fun ξ => ρ * L ξ) := by
    funext ξ
    simp only [add_sub_cancel_left,map_smul,smul_eq_mul]
  simp only [diskAverage,he,integral_const_mul,integral_linear_unitDisk,mul_zero]

lemma diskAverage_const (a : ℝ) (y : Plane) (ρ : ℝ) :
    diskAverage (fun _ => a) y ρ=a := by
  simp only [diskAverage,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change Real.pi⁻¹*(volume.real (Metric.ball (0:Plane) 1)*a)=a
  rw [volume_unit_disk_real]
  field_simp

lemma diskAverage_affine_error {f : Plane → ℝ} (hf : Smooth f) {C ρ : ℝ}
    (hC : 0≤C) (hρ : 0<ρ) (hess : ∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial f i) j z|≤C)
    (y : Plane) : |diskAverage f y ρ-f y|≤4*C*ρ^2 := by
  let L := fderiv ℝ f y
  let e := fun x : Plane => f x-f y-L (x-y)
  have he : Continuous e := hf.continuous.sub continuous_const |>.sub (L.continuous.comp (continuous_id.sub continuous_const))
  have hi := scaled_continuous_integrable he y ρ
  have havg : diskAverage e y ρ=diskAverage f y ρ-f y := by
    unfold diskAverage e
    rw [integral_sub (f:=fun ξ => f (y+ρ • ξ)-f y) (g:=fun ξ => L (y+ρ • ξ-y))
      ((scaled_continuous_integrable hf.continuous y ρ).sub (integrable_const _))
      (scaled_continuous_integrable (L.continuous.comp (continuous_id.sub continuous_const)) y ρ),
      integral_sub (scaled_continuous_integrable hf.continuous y ρ) (integrable_const _)]
    have hc := diskAverage_const (f y) y ρ
    have hl := diskAverage_linear L y ρ
    dsimp [diskAverage] at hc hl
    nlinarith
  rw [← havg]
  calc
    _ = Real.pi⁻¹ * ‖∫ξ in Metric.ball (0:Plane) 1,e (y+ρ • ξ)‖ := by
      simp only [diskAverage,abs_mul,abs_of_pos (inv_pos.mpr Real.pi_pos),Real.norm_eq_abs]
    _ ≤ Real.pi⁻¹ * (∫ξ in Metric.ball (0:Plane) 1,‖e (y+ρ • ξ)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ Real.pi⁻¹ * (∫_ξ in Metric.ball (0:Plane) 1,4*C*ρ^2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
      apply integral_mono_ae hi.norm (integrable_const _)
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with ξ hξ
      have hn : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hξ
      have hx : y+ρ • ξ∈Metric.closedBall y ρ := by
        simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
        nlinarith
      simpa only [e,L,Real.norm_eq_abs] using affine_error_bound_ball hf hρ.le hC (fun z _ => hess z) hx
    _ = 4*C*ρ^2 := diskAverage_const _ y ρ

lemma harmonic_outer_minus_average {f : Plane → ℝ} (hf : Smooth f) {C R ρ : ℝ}
    (hC : 0≤C) (hR : 0≤R) (hρ : 0<ρ)
    (hess : ∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial f i) j z|≤C)
    {y x : Plane} (hx : ‖x-y‖≤R*ρ) :
    f x-diskAverage f y ρ-(fderiv ℝ f y) (x-y)≤4*C*(R^2+1)*ρ^2 := by
  have he := (abs_le.mp (affine_error_bound_ball hf (by positivity : 0≤R*ρ) hC
    (fun z _ => hess z) (show x∈Metric.closedBall y (R*ρ) by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx))).2
  have hav := (abs_le.mp (diskAverage_affine_error hf hC hρ hess y)).1
  nlinarith

lemma quasiMeasurePreserving_affine {ρ : ℝ} (hρ : ρ≠0) (y : Plane) :
    Measure.QuasiMeasurePreserving (fun ξ : Plane => y+ρ • ξ) volume volume :=
  (measurePreserving_add_left volume y).quasiMeasurePreserving.comp (Measure.quasiMeasurePreserving_smul volume hρ)

lemma diskAverage_le_profileSup {V : Plane → EReal} {w : Plane → ℝ} {L : Plane →L[ℝ] ℝ}
    {y : Plane} {ρ : ℝ} (hρ : 0<ρ)
    (hi : IntegrableOn (fun ξ : Plane => w (y+ρ • ξ)) (Metric.ball 0 1))
    (he : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),V (y+ρ • ξ)=(w (y+ρ • ξ):EReal)) :
    (diskAverage w y ρ:EReal)≤⨆x∈Metric.ball y ρ,V x-(L (x-y):EReal) := by
  by_contra hh
  obtain ⟨b,hsb,hba⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hh)
  have hba' : b<diskAverage w y ρ := EReal.coe_lt_coe_iff.mp hba
  have hpoint : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),
      w (y+ρ • ξ)-L (y+ρ • ξ-y)≤b := by
    filter_upwards [he,self_mem_ae_restrict measurableSet_ball] with ξ hξ hmem
    have hnorm : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hmem
    have hx : y+ρ • ξ∈Metric.ball y ρ := by
      simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
      nlinarith
    have hs := (le_iSup₂_of_le (y+ρ • ξ) hx le_rfl).trans_lt hsb
    rw [hξ,← EReal.coe_sub] at hs
    exact (EReal.coe_lt_coe_iff.mp hs).le
  have hlin := scaled_continuous_integrable (f:=fun x => L (x-y)) (L.continuous.comp (continuous_id.sub continuous_const)) y ρ
  have hh := integral_mono_ae (hi.sub hlin) (integrable_const b) hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi hlin] at hh
  have he' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Real.pi_pos.le)
  have hz := diskAverage_linear L y ρ
  have hb := diskAverage_const b y ρ
  dsimp [diskAverage] at hz hb
  dsimp [diskAverage] at hba'
  nlinarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_finite_ae_D3 {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) :
    ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → V x≠⊥ ∧ V x≠⊤ := by
  obtain ⟨a,ha,hVa⟩ := hanchor
  have hb : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hb)
    (fun x hx => hneg x (hb hx))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (profile_lintegral_D8 hV hneg htest ha hVa))).2
  have hj := (ae_restrict_iff' measurableSet_ball).mp hi
  filter_upwards [hj] with x hx hm
  exact ⟨hx (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤8) hm),
    ne_top_of_le_ne_top (by simp) (hneg x (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000) hm))⟩

theorem potential_profile_affine_sup_bound {R : ℝ} (hR : 1≤R) : ∃Ck : ℝ,0≤Ck ∧
    ∀(ν : Measure Plane) [IsFiniteMeasure ν], (∀ᵐz ∂ν,‖z‖<4) →
    ∀(V : Plane → EReal) (h : Plane → ℝ),
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) → FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    Smooth h →
    (∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x) →
    ∀Ch : ℝ,0≤Ch → (∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial h i) j z|≤Ch) →
    ∀ρ : ℝ,0<ρ → ∀y : Plane,‖y‖≤1 → 2*R*ρ≤1 →
    let L := fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*R) ρ y z ∂ν)
    let e : ℝ := 4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν)
    (⨆x∈Metric.closedBall y (R*ρ),V x-(L (x-y):EReal))≤
      (⨆x∈Metric.ball y ρ,V x-(L (x-y):EReal))+(e:EReal) := by
  obtain ⟨Ck,hCk,hpot⟩ := ae_potential_affine_comparison (show 1≤2*R by linarith)
  refine ⟨Ck,hCk,?_⟩
  intro ν _ hs V h hV hneg htest hanchor hh heq Ch hCh hhess ρ hρ y hy hsmall
  dsimp only
  let L := fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*R) ρ y z ∂ν)
  let a := diskAverage h y ρ+∫z,logDiskAverage y ρ z ∂ν
  let e := 4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν)
  let U := Metric.ball y (2*R*ρ)
  have hRpos : 0<R := by linarith
  have hρsmall : ρ≤1 := by nlinarith
  have hU3 : U⊆Metric.ball (0:Plane) 3 := by
    intro x hx
    have hx' : ‖x-y‖<2*R*ρ := by simpa only [U,Metric.mem_ball,dist_eq_norm] using hx
    have hn := norm_add_le (x-y) y
    rw [sub_add_cancel] at hn
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  have hUΩ := hU3.trans (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000))
  have hupper : ∀x∈U,V x≤((a+L (x-y)+e:ℝ):EReal) := by
    apply profile_le_continuous_of_toReal_ae hV hneg htest Metric.isOpen_ball hUΩ
      ((continuous_const.add (L.continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hU3 (hpot ν hs ρ hρ y),
      ae_restrict_of_ae heq,self_mem_ae_restrict measurableSet_ball] with x hpx hex hmem
    have hx : ‖x-y‖≤(2*R)*ρ := (show ‖x-y‖<2*R*ρ by simpa only [U,Metric.mem_ball,dist_eq_norm] using hmem).le
    have hp := hpx hx
    have hh' := harmonic_outer_minus_average hh hCh (show 0≤2*R by positivity) hρ hhess hx
    rw [hex (hU3 hmem)]
    dsimp [a,L,e]
    change h x+aeLogPotential ν x≤diskAverage h y ρ+(∫z,logDiskAverage y ρ z ∂ν)+
      ((fderiv ℝ h y) (x-y)+inner ℝ (∫z,farGradient (2*R) ρ y z ∂ν) (x-y))+
      (4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν))
    linarith
  let w := fun x => h x+aeLogPotential ν x
  have hwi : IntegrableOn (fun ξ : Plane => w (y+ρ • ξ)) (Metric.ball 0 1) :=
    (scaled_continuous_integrable hh.continuous y ρ).add (scaled_aeLogPotential_integrableOn ν hs hρ y)
  have hfinite := profile_finite_ae_D3 hV hneg htest hanchor
  have hwV : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),V (y+ρ • ξ)=(w (y+ρ • ξ):EReal) := by
    filter_upwards [ae_restrict_of_ae ((quasiMeasurePreserving_affine hρ.ne' y).ae heq),
      ae_restrict_of_ae ((quasiMeasurePreserving_affine hρ.ne' y).ae hfinite),
      self_mem_ae_restrict measurableSet_ball] with ξ hξ hfξ hmem
    have hnorm : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hmem
    have h3 : y+ρ • ξ∈Metric.ball (0:Plane) 3 := by
      have hm := norm_add_le y (ρ • ξ)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ] at hm
      simp only [Metric.mem_ball,dist_zero_right]
      nlinarith
    rw [← EReal.coe_toReal (hfξ h3).2 (hfξ h3).1,hξ h3]
  have hav : diskAverage w y ρ=a := by
    dsimp [diskAverage,w,a]
    rw [integral_add (scaled_continuous_integrable hh.continuous y ρ) (scaled_aeLogPotential_integrableOn ν hs hρ y),
      integral_logDiskAverage ν hs hρ y]
    ring
  have hinner := diskAverage_le_profileSup (L:=L) hρ hwi hwV
  rw [hav] at hinner
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hxU : x∈U := by
    have hx' : ‖x-y‖≤R*ρ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    simp only [U,Metric.mem_ball,dist_eq_norm]
    nlinarith
  have hhx : V x-(L (x-y):EReal)≤((a+e:ℝ):EReal) := by
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr
    simpa only [← EReal.coe_add,add_assoc,add_comm,add_left_comm] using hupper x hxU
  exact hhx.trans (by simpa only [L,e,EReal.coe_add] using add_le_add hinner (le_refl (e:EReal)))

end SharpNodal.Profiles

end
end
end
end
end
end
end

end OAI
