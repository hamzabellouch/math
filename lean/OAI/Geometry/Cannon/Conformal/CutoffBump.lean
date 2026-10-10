import Mathlib
import OAI.Geometry.Cannon.Conformal.ImageArea
import OAI.Geometry.Cannon.Beltrami.MultiplyLp

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace CannonMetricQC
open Set Metric Filter
open scoped Topology ContDiff NNReal

def cutoffBump (R : ℝ) : ContDiffBump (0:ℂ) :=
    {rIn := max R 0+1
     rOut := max R 0+2
     rIn_pos := by linarith [le_max_right R 0]
     rIn_lt_rOut := by linarith}

def smoothCutoff (R : ℝ) (x : ℂ) : ℂ := (cutoffBump R x:ℂ)

lemma smoothCutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (smoothCutoff R) :=
  Complex.ofRealCLM.contDiff.comp (cutoffBump R).contDiff

lemma smoothCutoff_support (R : ℝ) : HasCompactSupport (smoothCutoff R) :=
  (cutoffBump R).hasCompactSupport.comp_left (show ((0:ℝ):ℂ)=0 from Complex.ofReal_zero)

lemma smoothCutoff_lipschitz (R : ℝ) : ∃ L, LipschitzWith L (smoothCutoff R) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (smoothCutoff_support R)
    (smoothCutoff_smooth R) (by simp)

lemma smoothCutoff_bound (R : ℝ) (x : ℂ) : ‖smoothCutoff R x‖ ≤ 1 := by
  simpa only [smoothCutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (cutoffBump R).nonneg] using (cutoffBump R).le_one (x:=x)

lemma smoothCutoff_zero (R : ℝ) (x : ℂ) (hx : max R 0+2 < ‖x‖) : smoothCutoff R x=0 := by
  have hz := (cutoffBump R).zero_of_le_dist (x:=x) (by simpa [cutoffBump,dist_zero_right] using hx.le)
  simp only [smoothCutoff,hz,Complex.ofReal_zero]

lemma smoothCutoff_one (R : ℝ) (x : ℂ) (hx : x ∈ closedBall (0:ℂ) R) :
    smoothCutoff R =ᶠ[𝓝 x] fun _ => (1:ℂ) := by
  have hx' : x ∈ ball (0:ℂ) (cutoffBump R).rIn := by
    have hh : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
    simp only [mem_ball,dist_zero_right,cutoffBump]
    linarith [le_max_left R 0]
  filter_upwards [(cutoffBump R).eventuallyEq_one_of_mem_ball hx'] with y hy
  simpa only [smoothCutoff,Pi.one_apply,Complex.ofReal_one] using congrArg (fun t : ℝ => (t:ℂ)) hy

lemma exists_smooth_cutoff (R : ℝ) :
    ∃ (χ : ℂ → ℂ) (L : ℝ≥0) (B : ℝ), 0 ≤ B ∧
      ContDiff ℝ ∞ χ ∧ LipschitzWith L χ ∧ (∀ x, ‖χ x‖ ≤ 1) ∧
      (∀ x, B < ‖x‖ → χ x=0) ∧
      (∀ x ∈ closedBall (0:ℂ) R, χ =ᶠ[𝓝 x] fun _ => (1:ℂ)) := by
  obtain ⟨L,hL⟩ := smoothCutoff_lipschitz R
  exact ⟨smoothCutoff R,L,max R 0+2,by linarith [le_max_right R 0],
    smoothCutoff_smooth R,hL,smoothCutoff_bound R,smoothCutoff_zero R,smoothCutoff_one R⟩

lemma cutoff_fderiv_eq {f χ : ℂ → ℂ} {x : ℂ} (hχ : χ =ᶠ[𝓝 x] fun _ => (1:ℂ)) :
    fderiv ℝ (fun y => χ y*f y) x=fderiv ℝ f x := by
  apply EventuallyEq.fderiv_eq
  exact hχ.mono (fun y hy => by simp only [hy,one_mul])
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal NNReal ContDiff

theorem weakQS_local_weakW12 (f : ℂ ≃ₜ ℂ) {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) (R : ℝ) (v : ℂ) :
    MemLp (fun x => fderiv ℝ (f : ℂ → ℂ) x v) 2
      (volume.restrict (closedBall (0:ℂ) R)) ∧
    ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ closedBall (0:ℂ) R →
      (∫ z, φ z*fderiv ℝ (f : ℂ → ℂ) z v)=
        -(∫ z, (fderiv ℝ (φ : ℂ → ℂ) z v)*f z) := by
  obtain ⟨χ,L,B,hB,hχd,hχL,hχb,hχs,hχone⟩ := exists_smooth_cutoff R
  obtain ⟨hF,C,hC,hinc⟩ := weakQS_cutoff_increment_bound f hH hf χ hχL hχb hB hχs
  have hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ (fun y => χ y*f y) x := by
    filter_upwards [weakQS_ae_differentiable f hH hf] with x hx
    exact ((hχd.differentiable (by simp)).differentiableAt).mul hx
  obtain ⟨hm,hw⟩ := CannonBeltrami.weak_fderiv_of_increment_bound hF hFd hC hinc v
  have he (x : ℂ) (hx : x ∈ closedBall (0:ℂ) R) :
      fderiv ℝ (fun y => χ y*f y) x=fderiv ℝ (f : ℂ → ℂ) x :=
    cutoff_fderiv_eq (hχone x hx)
  refine ⟨(hm.restrict (closedBall (0:ℂ) R)).ae_eq ?_,fun φ hφ => ?_⟩
  · filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
    exact congrArg (fun D : ℂ →L[ℝ] ℂ => D v) (he x hx)
  · have hleft : (fun z => φ z*fderiv ℝ (fun y => χ y*f y) z v)=
        (fun z => φ z*fderiv ℝ (f : ℂ → ℂ) z v) := by
      funext z
      by_cases hz : z ∈ closedBall (0:ℂ) R
      · rw [he z hz]
      · have hzero : φ z=0 := Function.notMem_support.mp (fun h => hz (hφ (subset_closure h)))
        simp only [hzero,zero_mul]
    have hright : (fun z => (fderiv ℝ (φ : ℂ → ℂ) z v)*(χ z*f z))=
        (fun z => (fderiv ℝ (φ : ℂ → ℂ) z v)*f z) := by
      funext z
      by_cases hz : z ∈ closedBall (0:ℂ) R
      · rw [(hχone z hz).eq_of_nhds,one_mul]
      · have hzero : fderiv ℝ (φ : ℂ → ℂ) z=0 :=
          Function.notMem_support.mp (fun h => hz (hφ (support_fderiv_subset ℝ h)))
        simp only [hzero,zero_apply,zero_mul]
    simpa only [show (fun z => φ z*fderiv ℝ (fun y => χ y*f y) z v)=
      (fun z => φ z*fderiv ℝ (f : ℂ → ℂ) z v) from hleft,hright] using hw φ
end CannonMetricQC
noncomputable section
namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

lemma norm_integral_sq_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {g : X → ℂ} (hg : Integrable g ν)
    (hgs : Integrable (fun x => ‖g x‖^2) ν) :
    ‖∫ x, g x ∂ν‖^2 ≤ ∫ x, ‖g x‖^2 ∂ν := by
  exact ((convexOn_norm (E:=ℂ) convex_univ).pow (fun _ _ => norm_nonneg _) 2).map_integral_le
    (continuous_norm.pow 2).continuousOn isClosed_univ (.of_forall fun _ => mem_univ _) hg hgs

theorem kernel_energy_pointwise {κ : ℂ → ℝ} (hκ : Continuous κ)
    (hc : HasCompactSupport κ) (hp : ∀ x, 0 ≤ κ x) (hi : ∫ x, κ x=1)
    {V : ℂ → ℂ} (hV : LocallyIntegrable V volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume) (x : ℂ) :
    ENNReal.ofReal (‖(κ ⋆[lsmul ℝ ℝ,volume] V) x‖^2) ≤
      ∫⁻ y, ENNReal.ofReal (κ y)*ENNReal.ofReal (‖V (x-y)‖^2) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal (κ y))
  have hm : Measurable (fun y => ENNReal.ofReal (κ y)) := hκ.measurable.ennreal_ofReal
  have ht : ∀ᵐ y ∂volume, ENNReal.ofReal (κ y) < ∞ := .of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hv : ν univ=1 := by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hκ.integrable_of_hasCompactSupport hc) (.of_forall hp),hi]
    norm_num
  let : IsProbabilityMeasure ν := ⟨hv⟩
  have hVi : Integrable (fun y => V (x-y)) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hm ht).mpr
    simpa only [ENNReal.toReal_ofReal (hp _),ConvolutionExistsAt,lsmul_apply] using
      hc.convolutionExists_left (lsmul ℝ ℝ) hκ hV x
  have hVsi : Integrable (fun y => ‖V (x-y)‖^2) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hm ht).mpr
    simpa only [ENNReal.toReal_ofReal (hp _),smul_eq_mul,ConvolutionExistsAt,mul_apply'] using
      hc.convolutionExists_left (mul ℝ ℝ) hκ hVs x
  have he : (∫ y, V (x-y) ∂ν)=(κ ⋆[lsmul ℝ ℝ,volume] V) x := by
    rw [integral_withDensity_eq_integral_toReal_smul hm ht]
    simp only [ENNReal.toReal_ofReal (hp _),convolution,lsmul_apply]
  have h := norm_integral_sq_le ν hVi hVsi
  rw [he] at h
  calc
    _ ≤ ENNReal.ofReal (∫ y, ‖V (x-y)‖^2 ∂ν) := ENNReal.ofReal_le_ofReal h
    _ = ∫⁻ y, ENNReal.ofReal (‖V (x-y)‖^2) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hVsi (.of_forall fun _ => sq_nonneg _)
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul₀' (μ:=volume) hm.aemeasurable hVsi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
      rfl

lemma translated_ball_energy_le (e : ℂ → ℝ≥0∞) (c y : ℂ) {R r : ℝ}
    (hy : ‖y‖ ≤ r) :
    (∫⁻ x in closedBall c R, e (x-y)) ≤ ∫⁻ z in closedBall c (R+r), e z := by
  rw [← lintegral_indicator isClosed_closedBall.measurableSet,
    ← lintegral_indicator isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ x, (closedBall c (R+r)).indicator e (x-y) := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ closedBall c R
      · have hx' : x-y ∈ closedBall c (R+r) := by
          have he : x-y-c=(x-c)-y := by abel
          have hh : ‖x-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hx
          simp only [mem_closedBall,dist_eq_norm,he]
          exact (norm_sub_le _ _).trans (add_le_add hh hy)
        simp only [indicator_of_mem hx,indicator_of_mem hx',le_refl]
      · simp only [indicator_of_notMem hx,zero_le]
    _ = _ := lintegral_sub_right_eq_self _ y

theorem kernel_energy_local {κ : ℂ → ℝ} (hκ : Continuous κ)
    (hc : HasCompactSupport κ) (hp : ∀ x, 0 ≤ κ x) (hi : ∫ x, κ x=1)
    {V : ℂ → ℂ} (hVm : Measurable V) (hV : LocallyIntegrable V volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    {r : ℝ} (hs : ∀ y, κ y ≠ 0 → ‖y‖ ≤ r) (c : ℂ) (R : ℝ) :
    (∫⁻ x in closedBall c R, ENNReal.ofReal (‖(κ ⋆[lsmul ℝ ℝ,volume] V) x‖^2)) ≤
      ∫⁻ z in closedBall c (R+r), ENNReal.ofReal (‖V z‖^2) := by
  let e : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖V z‖^2)
  have he : Measurable e := (hVm.norm.pow_const 2).ennreal_ofReal
  have hκm : Measurable (fun y => ENNReal.ofReal (κ y)) := hκ.measurable.ennreal_ofReal
  have hm : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (κ p.2)*e (p.1-p.2)) :=
    (hκm.comp measurable_snd).mul (he.comp (measurable_fst.sub measurable_snd))
  have hi' : (∫⁻ y, ENNReal.ofReal (κ y))=1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hκ.integrable_of_hasCompactSupport hc) (.of_forall hp),hi]
    norm_num
  calc
    _ ≤ ∫⁻ x in closedBall c R, ∫⁻ y, ENNReal.ofReal (κ y)*e (x-y) :=
      lintegral_mono (kernel_energy_pointwise hκ hc hp hi hV hVs)
    _ = ∫⁻ y, ∫⁻ x in closedBall c R, ENNReal.ofReal (κ y)*e (x-y) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (κ y)*(∫⁻ x in closedBall c R, e (x-y)) := by
      apply lintegral_congr
      intro y
      exact lintegral_const_mul _ (he.comp (measurable_id.sub_const y))
    _ ≤ ∫⁻ y, ENNReal.ofReal (κ y)*(∫⁻ z in closedBall c (R+r), e z) := by
      apply lintegral_mono
      intro y
      by_cases hy : κ y=0
      · simp only [hy,ENNReal.ofReal_zero,zero_mul,le_refl]
      · exact mul_le_mul_right (translated_ball_energy_le e c y (hs y hy)) _
    _ = _ := by rw [lintegral_mul_const _ hκm,hi',one_mul]
end CannonMetricQC
noncomputable section
namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ContDiff

lemma convolution_directional {F κ : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x v : ℂ) :
    fderiv ℝ (F ⋆[mul ℝ ℂ,volume] κ) x v=
      ∫ z, F z*fderiv ℝ κ (x-z) v := by
  let L := mul ℝ ℂ
  let D : ℂ → (ℂ →L[ℝ] ℂ) := fun z => L.precompR ℂ (F z) (fderiv ℝ κ (x-z))
  have hD : Integrable D volume :=
    (hc.fderiv ℝ).convolutionExists_right (L.precompR ℂ) hF
      ((hκ.of_le (by simp) : ContDiff ℝ 1 κ).continuous_fderiv (by simp)) x
  have hd := hc.hasFDerivAt_convolution_right L hF (hκ.of_le (by simp)) x
  rw [hd.fderiv]
  change (∫ z, D z) v=_
  rw [ContinuousLinearMap.integral_apply hD]
  rfl

lemma fderiv_reflect {κ : ℂ → ℂ} (hκ : Differentiable ℝ κ) (x z v : ℂ) :
    fderiv ℝ (fun w => κ (x-w)) z v = - fderiv ℝ κ (x-z) v := by
  have hd := (hκ (x-z)).hasFDerivAt.comp z ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
  change fderiv ℝ (κ ∘ fun w => x-w) z v=_
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,zero_sub,neg_apply,map_neg]

theorem weak_derivative_convolution {F V κ : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (v : ℂ) (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*F z))
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : ℂ) :
    fderiv ℝ (F ⋆[mul ℝ ℂ,volume] κ) x v=
      (V ⋆[mul ℝ ℂ,volume] κ) x := by
  rw [convolution_directional hF hκ hc]
  let ψ : ℂ → ℂ := fun z => κ (x-z)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ :=
    hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addLeft x))
  let φ := hcψ.toSchwartzMap hψ
  have hh := hw φ hcψ
  have he (z : ℂ) : fderiv ℝ (φ : ℂ → ℂ) z v= -fderiv ℝ κ (x-z) v :=
    fderiv_reflect (hκ.differentiable (by simp)) x z v
  simp only [he,neg_mul,integral_neg,neg_neg] at hh
  change (∫ z, F z*fderiv ℝ κ (x-z) v)=∫ z, V z*κ (x-z)
  have hh' : (∫ z, κ (x-z)*V z)=∫ z, fderiv ℝ κ (x-z) v*F z := hh
  simpa only [mul_comm] using hh'.symm
end CannonMetricQC

namespace CannonMetricQC
open MeasureTheory Set Metric Filter Function ContinuousLinearMap
open scoped Topology Convolution ENNReal NNReal

def mollifier (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ)+1)
  rOut := 2 / ((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply (div_lt_div_iff_of_pos_right (by positivity)).mpr; norm_num

def mollify (μ : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] μ

lemma mollify_smooth {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify μ n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifier n).contDiff_normed hm

lemma mollify_eq_complex_convolution (F : ℂ → ℂ) (n : ℕ) :
    mollify F n = F ⋆[mul ℝ ℂ,volume] (fun z => ((mollifier n).normed volume z:ℂ)) := by
  rw [← convolution_flip]
  funext x
  unfold mollify convolution
  apply integral_congr_ae
  exact .of_forall (fun z => by simp [mul_comm,lsmul_apply])

lemma mollifier_radius_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  simpa [mollifier,div_eq_mul_inv] using h

lemma mollify_locally_uniform {F : ℂ → ℂ} (hF : Continuous F) :
    TendstoLocallyUniformly (mollify F) F atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have ht : Tendsto (fun p : ℕ × ℂ => mollify F p.1 p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (F x)) := by
    apply ContDiffBump.convolution_tendsto_right
    · exact mollifier_radius_tendsto.comp tendsto_fst
    · exact .of_forall (fun _ => hF.aestronglyMeasurable)
    · exact (hF.tendsto x).comp tendsto_snd
    · exact tendsto_snd
  exact ((hF.tendsto x).comp tendsto_snd).prodMk_nhds ht |>.mono_right (nhds_le_uniformity (F x))

lemma plane_opNorm_le (D : ℂ →L[ℝ] ℂ) : ‖D‖ ≤ ‖D 1‖+‖D Complex.I‖ := by
  apply D.opNorm_le_bound (by positivity)
  intro z
  have he : z=z.re • (1:ℂ)+z.im • Complex.I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,mul_one] using (Complex.re_add_im z).symm
  calc
    ‖D z‖ = ‖z.re • D 1+z.im • D Complex.I‖ := by conv_lhs => rw [he,map_add,map_smul,map_smul]
    _ ≤ ‖z.re • D 1‖+‖z.im • D Complex.I‖ := norm_add_le _ _
    _ = |z.re| * ‖D 1‖+|z.im| * ‖D Complex.I‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖z‖*‖D 1‖+‖z‖*‖D Complex.I‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = _ := by ring

lemma plane_opNorm_sq (D : ℂ →L[ℝ] ℂ) :
    ‖D‖^2 ≤ 2*(‖D 1‖^2+‖D Complex.I‖^2) := by
  have h := (sq_le_sq₀ (norm_nonneg D) (by positivity)).mpr (plane_opNorm_le D)
  nlinarith [sq_nonneg (‖D 1‖-‖D Complex.I‖)]

lemma mollify_directional {F V : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (v : ℂ) (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*F z)) (n : ℕ) (x : ℂ) :
    fderiv ℝ (mollify F n) x v=mollify V n x := by
  rw [mollify_eq_complex_convolution,mollify_eq_complex_convolution]
  exact weak_derivative_convolution hF v hw
    (Complex.ofRealCLM.contDiff.comp (mollifier n).contDiff_normed)
    ((mollifier n).hasCompactSupport_normed.comp_left Complex.ofReal_zero) x

lemma mollify_energy_local {V : ℂ → ℂ} (hVm : Measurable V)
    (hV : LocallyIntegrable V volume) (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (n : ℕ) (c : ℂ) (R : ℝ) :
    (∫⁻ x in closedBall c R, ENNReal.ofReal (‖mollify V n x‖^2)) ≤
      ∫⁻ z in closedBall c (R+(mollifier n).rOut), ENNReal.ofReal (‖V z‖^2) := by
  apply kernel_energy_local (mollifier n).continuous_normed
    (mollifier n).hasCompactSupport_normed (mollifier n).nonneg_normed
    (mollifier n).integral_normed hVm hV hVs
  intro y hy
  have h : y ∈ Function.support ((mollifier n).normed volume) := hy
  rw [(mollifier n).support_normed_eq] at h
  exact (show ‖y‖ < (mollifier n).rOut by simpa only [mem_ball,dist_zero_right] using h).le

theorem mollify_opNorm_energy {F V W : ℂ → ℂ} (hF : Continuous F)
    (hVm : Measurable V) (hWm : Measurable W)
    (hV : LocallyIntegrable V volume) (hW : LocallyIntegrable W volume)
    (hVs : LocallyIntegrable (fun x => ‖V x‖^2) volume)
    (hWs : LocallyIntegrable (fun x => ‖W x‖^2) volume)
    (hv : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*V z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z 1*F z))
    (hw : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, φ z*W z)= -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z Complex.I*F z))
    (n : ℕ) (c : ℂ) (R : ℝ) :
    ENNReal.ofReal (∫ x in closedBall c R, ‖fderiv ℝ (mollify F n) x‖^2) ≤
      2*(∫⁻ z in closedBall c (R+(mollifier n).rOut),
        ENNReal.ofReal (‖V z‖^2+‖W z‖^2)) := by
  have hd := (mollify_smooth hF.locallyIntegrable n).continuous_fderiv (by simp)
  have hi : IntegrableOn (fun x => ‖fderiv ℝ (mollify F n) x‖^2) (closedBall c R) volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall c R)
  rw [ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun _ => sq_nonneg _)]
  have hMv := (mollify_smooth hV n).continuous
  have hMw := (mollify_smooth hW n).continuous
  calc
    _ ≤ ∫⁻ x in closedBall c R, 2*(ENNReal.ofReal (‖mollify V n x‖^2)+
        ENNReal.ofReal (‖mollify W n x‖^2)) := by
      apply lintegral_mono
      intro x
      have hh := plane_opNorm_sq (fderiv ℝ (mollify F n) x)
      rw [mollify_directional hF.locallyIntegrable 1 hv,
        mollify_directional hF.locallyIntegrable Complex.I hw] at hh
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using ENNReal.ofReal_le_ofReal hh
    _ = 2*((∫⁻ x in closedBall c R, ENNReal.ofReal (‖mollify V n x‖^2))+
        ∫⁻ x in closedBall c R, ENNReal.ofReal (‖mollify W n x‖^2)) := by
      have hme : Measurable (fun x => ENNReal.ofReal (‖mollify V n x‖^2)+
          ENNReal.ofReal (‖mollify W n x‖^2)) :=
        (hMv.norm.pow 2).measurable.ennreal_ofReal.add (hMw.norm.pow 2).measurable.ennreal_ofReal
      have hmeV : Measurable (fun x => ENNReal.ofReal (‖mollify V n x‖^2)) :=
        (hMv.norm.pow 2).measurable.ennreal_ofReal
      rw [lintegral_const_mul _ hme,lintegral_add_left hmeV]
    _ ≤ 2*((∫⁻ z in closedBall c (R+(mollifier n).rOut), ENNReal.ofReal (‖V z‖^2))+
        ∫⁻ z in closedBall c (R+(mollifier n).rOut), ENNReal.ofReal (‖W z‖^2)) :=
      mul_le_mul_right (add_le_add (mollify_energy_local hVm hV hVs n c R)
        (mollify_energy_local hWm hW hWs n c R)) 2
    _ = _ := by
      simp only [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      rw [lintegral_add_left (hVm.norm.pow_const 2).ennreal_ofReal]
end CannonMetricQC

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
end
end
end

end OAI
