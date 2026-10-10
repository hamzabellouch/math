import Mathlib
import OAI.Geometry.Cannon.Beltrami.RectCrossing

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane
open Set Metric MeasureTheory

lemma realProd_to_complex_norm (p : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm p‖ ≤ 2*‖p‖ := by
  rw [Complex.equivRealProdCLM_symm_apply]
  calc
    _ ≤ ‖(p.1:ℂ)‖+‖(p.2:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = ‖p.1‖+‖p.2‖ := by simp
    _ ≤ 2*‖p‖ := by have h1 := norm_fst_le p; have h2 := norm_snd_le p; linarith

lemma realProd_to_complex_opNorm : ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖ ≤ 2 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) realProd_to_complex_norm

def planeBox (R : ℝ) : Set ℂ := Complex.equivRealProdCLM ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R)

lemma planeBox_compact (R : ℝ) : IsCompact (planeBox R) :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)

lemma closedBall_subset_planeBox (R : ℝ) : closedBall (0:ℂ) R ⊆ planeBox R := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by simpa using hz
  have hr := Complex.abs_re_le_norm z |>.trans hz'
  have hi := Complex.abs_im_le_norm z |>.trans hz'
  exact ⟨abs_le.mp hr,abs_le.mp hi⟩

lemma coordinate_energy_bound (u : ℂ → ℝ) (hu : ContDiff ℝ 1 u) (R : ℝ) :
    (∫ p in Icc (-R) R ×ˢ Icc (-R) R, ‖fderiv ℝ (u ∘ Complex.equivRealProdCLM.symm) p‖^2) ≤
      4*(∫ z in planeBox R, ‖fderiv ℝ u z‖^2) := by
  let e := Complex.equivRealProdCLM.symm
  let S := Icc (-R) R ×ˢ Icc (-R) R
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcomp : ContDiff ℝ 1 (u ∘ e) := hu.comp e.contDiff
  have hq : Continuous (fun p => ‖fderiv ℝ u (e p)‖^2) :=
    ((hu.continuous_fderiv (by simp)).comp e.continuous).norm.pow 2
  have hchange : (∫ z in planeBox R, ‖fderiv ℝ u z‖^2) =
      ∫ p in S, ‖fderiv ℝ u (e p)‖^2 := by
    have H := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding (fun p => ‖fderiv ℝ u (e p)‖^2) S
    simpa only [Complex.measurableEquivRealProd,Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph,ContinuousLinearEquiv.symm_apply_apply,e,planeBox] using H
  rw [hchange,← integral_const_mul]
  apply setIntegral_mono_on
    ((hcomp.continuous_fderiv (by simp)).norm.pow 2 |>.continuousOn.integrableOn_compact hS)
    ((hq.const_mul 4).continuousOn.integrableOn_compact hS) hS.measurableSet
  intro p hp
  change ‖fderiv ℝ (u ∘ e) p‖^2 ≤ 4*‖fderiv ℝ u (e p)‖^2
  rw [fderiv_comp p (hu.differentiable (by simp) (e p)) e.differentiableAt,e.fderiv]
  have hc := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ u (e p)) e.toContinuousLinearMap
  have hn := hc.trans (mul_le_mul_of_nonneg_left realProd_to_complex_opNorm (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖fderiv ℝ u (e p)‖*2)).mpr hn
  nlinarith

theorem plane_continuum_capacity (u : ℂ → ℝ) (hu : ContDiff ℝ 1 u)
    {E F : Set ℂ} (hEc : IsPreconnected E) (hFc : IsPreconnected F)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hEB : E ⊆ closedBall 0 R) (hFB : F ⊆ closedBall 0 R)
    (hE : ∀ z ∈ E, u z=0) (hF : ∀ z ∈ F, u z=1)
    (hdE : ∃ p ∈ E, ∃ q ∈ E, δ ≤ dist p q)
    (hdF : ∃ p ∈ F, ∃ q ∈ F, δ ≤ dist p q) :
    1 ≤ 32*(4*R/δ+1)*(∫ z in planeBox R, ‖fderiv ℝ u z‖^2) := by
  let e := Complex.equivRealProdCLM
  have hwide (T : Set ℂ) (hT : ∃ p ∈ T, ∃ q ∈ T, δ ≤ dist p q) :
      ∃ p ∈ e '' T, ∃ q ∈ e '' T, δ/2 ≤ dist p q := by
    obtain ⟨p,hp,q,hq,hd⟩ := hT
    refine ⟨e p,⟨p,hp,rfl⟩,e q,⟨q,hq,rfl⟩,?_⟩
    have hh := realProd_to_complex_norm (e p-e q)
    rw [map_sub,e.symm_apply_apply,e.symm_apply_apply] at hh
    rw [dist_eq_norm] at hd ⊢
    linarith
  have hbox (T : Set ℂ) (hT : T ⊆ closedBall 0 R) :
      e '' T ⊆ Icc (-R) R ×ˢ Icc (-R) R := by
    rintro p ⟨z,hz,rfl⟩
    exact closedBall_subset_planeBox R (hT hz)
  have H := CannonRealPlane.continuum_capacity_bound (hu.comp e.symm.contDiff)
    (hEc.image e e.continuous.continuousOn) (hFc.image e e.continuous.continuousOn)
    (by linarith : -R < R) (by positivity : 0 < δ/2) (hbox E hEB) (hbox F hFB)
    (by rintro p ⟨z,hz,rfl⟩; simpa only [Function.comp_apply,e.symm_apply_apply] using hE z hz)
    (by rintro p ⟨z,hz,rfl⟩; simpa only [Function.comp_apply,e.symm_apply_apply] using hF z hz)
    (hwide E hdE) (hwide F hdF)
  have henergy := coordinate_energy_bound u hu R
  have hC : 0 ≤ 8*((R- -R)/(δ/2)+1) := by
    have : 0 ≤ R- -R := by linarith
    positivity
  have hh := mul_le_mul_of_nonneg_left henergy hC
  have hid : 8*((R- -R)/(δ/2)+1)*4=32*(4*R/δ+1) := by ring
  rw [← mul_assoc,hid] at hh
  exact H.trans hh

end CannonPlane

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonPlane

lemma smoothTransition_deriv_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t=0 := by
  rcases ht with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
      exact Real.smoothTransition.zero_of_nonpos hx.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact Real.smoothTransition.one_of_one_le hx.le
    simpa only [deriv_const] using he.deriv_eq

lemma smoothTransition_deriv_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (fun t => |deriv Real.smoothTransition t|) :=
    (Real.smoothTransition.contDiff (n:=1) |>.continuous_deriv (by simp)).abs
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).bddAbove_image hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · exact (hC ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  · have ht' : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
    rw [smoothTransition_deriv_zero ht',abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)

def annularCutoff (r R : ℝ) (z : ℂ) : ℝ :=
  Real.smoothTransition (Real.log (‖z‖/r)/Real.log (R/r))

lemma annularCutoff_inner {r R : ℝ} (hr : 0 < r) (hrR : r < R) {z : ℂ} (hz : ‖z‖ ≤ r) :
    annularCutoff r R z=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hL : 0 < Real.log (R/r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply div_nonpos_of_nonpos_of_nonneg _ hL.le
  exact Real.log_nonpos (div_nonneg (norm_nonneg _) hr.le) ((div_le_one hr).mpr hz)

lemma annularCutoff_outer {r R : ℝ} (hr : 0 < r) (hrR : r < R) {z : ℂ} (hz : R ≤ ‖z‖) :
    annularCutoff r R z=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hL : 0 < Real.log (R/r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply (one_le_div hL).mpr
  exact Real.log_le_log (div_pos (hr.trans hrR) hr) (div_le_div_of_nonneg_right hz hr.le)

lemma annularCutoff_contDiff {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ContDiff ℝ ∞ (annularCutoff r R) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    have he : annularCutoff r R =ᶠ[𝓝 (0:ℂ)] fun _ => (0:ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with z hz
      apply annularCutoff_inner hr hrR
      exact (show ‖z‖ < r by simpa only [mem_ball,dist_zero_right] using hz).le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Real.smoothTransition.contDiffAt.comp z
      (((contDiffAt_id.norm ℝ hz).div_const r).log (div_ne_zero (norm_ne_zero_iff.mpr hz) hr.ne') |>.div_const _)

lemma annularCutoff_fderiv_zero_inner {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : ‖z‖ < r) : fderiv ℝ (annularCutoff r R) z=0 := by
  have he : annularCutoff r R =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact annularCutoff_inner hr hrR hw.le
  simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜:=ℝ)

lemma annularCutoff_fderiv_zero_outer {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z : ℂ} (hz : R < ‖z‖) : fderiv ℝ (annularCutoff r R) z=0 := by
  have he : annularCutoff r R =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact annularCutoff_outer hr hrR hw.le
  simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜:=ℝ)

lemma annularCutoff_fderiv_bound {r R C : ℝ} (hr : 0 < r) (hrR : r < R)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (annularCutoff r R) z‖ ≤ C/(Real.log (R/r)*‖z‖) := by
  let L := Real.log (R/r)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_id.norm ℝ hz : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z).differentiableAt (by simp)
  have hdiv : HasFDerivAt (fun w : ℂ => ‖w‖/r) (r⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z) z := by
    simpa only [Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hn.hasFDerivAt.const_smul r⁻¹
  have hlog := (Real.hasDerivAt_log (div_ne_zero hzn.ne' hr.ne')).comp_hasFDerivAt z hdiv
  have hscale : HasFDerivAt (fun w : ℂ => Real.log (‖w‖/r)/L)
      (L⁻¹ • ((‖z‖/r)⁻¹ • (r⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z))) z := by
    simpa only [Function.comp_def,Pi.smul_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hlog.const_smul L⁻¹
  have ht := (Real.smoothTransition.contDiff (n:=1) |>.differentiable (by simp) (Real.log (‖z‖/r)/L)).hasDerivAt
  have hd := ht.comp_hasFDerivAt z hscale
  change HasFDerivAt (annularCutoff r R) _ z at hd
  rw [hd.fderiv]
  simp only [norm_smul,Real.norm_eq_abs]
  rw [norm_fderiv_norm hn]
  simp only [abs_inv,abs_of_pos hr,abs_of_pos hL,abs_of_pos (div_pos hzn hr)]
  calc
    _ = |deriv Real.smoothTransition (Real.log (‖z‖/r)/L)|/(L*‖z‖) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (hC _) (mul_pos hL hzn).le

end CannonPlane

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
