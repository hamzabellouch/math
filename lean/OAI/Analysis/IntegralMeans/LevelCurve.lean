import OAI.Analysis.IntegralMeans.Winding

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def periodicLoop {γ : ℝ → ℂ} (hc : Continuous γ) (s : ℝ) : C(unitInterval,ℂ) :=
  ⟨fun t => γ ((t : ℝ)+s),hc.comp (continuous_subtype_val.add continuous_const)⟩

lemma periodicLoop_closed {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (s : ℝ) :
    periodicLoop hc s 1 = periodicLoop hc s 0 := by
  simpa only [periodicLoop,ContinuousMap.coe_mk,show ((1 : unitInterval) : ℝ) = 1 from rfl,show ((0 : unitInterval) : ℝ) = 0 from rfl,
    zero_add,add_zero,add_comm] using hp s

lemma periodicLoop_range {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (s : ℝ) : range (periodicLoop hc s) = range γ := by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩; exact ⟨(t : ℝ)+s,rfl⟩
  · rintro _ ⟨t,rfl⟩
    obtain ⟨u,hu,he⟩ := hp.exists_mem_Ico (by norm_num) t s
    refine ⟨⟨u-s,⟨by linarith [hu.1],by linarith [hu.2]⟩⟩,?_⟩
    simpa only [periodicLoop,ContinuousMap.coe_mk,sub_add_cancel] using he.symm

lemma loopIndex_periodic_shift {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) {a : ℂ} (ha : a ∉ range γ) (s : ℝ) :
    loopIndex (periodicLoop hc s) a = loopIndex (periodicLoop hc 0) a := by
  let H : C(unitInterval × unitInterval,ℂ) :=
    ⟨fun p => γ ((p.2 : ℝ)+(p.1 : ℝ)*s)-a,by fun_prop⟩
  have hi := windingNumber_homotopy H (by
    intro p; exact sub_ne_zero.mpr (fun he => ha ⟨_,he⟩)) (by
    intro t
    change γ (1+(t:ℝ)*s)-a = γ (0+(t:ℝ)*s)-a
    simpa only [zero_add,add_zero,add_comm] using congrArg (fun z : ℂ => z-a) (hp ((t:ℝ)*s)))
  simpa only [H,loopIndex,periodicLoop,show ((1 : unitInterval) : ℝ) = 1 from rfl,show ((0 : unitInterval) : ℝ) = 0 from rfl,
    ContinuousMap.coe_mk,one_mul,zero_mul] using hi

lemma transverse_displacement_not_mem {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    {d : ℂ} {δ : ℝ}
    (hz : ∀ w : ℂ, |w.re| ≤ δ → |w.im| ≤ 1/2 →
      (γ w.im-γ 0-w.re • (Complex.I*d) = 0 ↔ w = 0))
    {r : ℝ} (hr : r ≠ 0) (hrd : |r| ≤ δ) :
    γ 0+r • (Complex.I*d) ∉ range γ := by
  rintro ⟨t,ht⟩
  obtain ⟨u,hu,he⟩ := hp.exists_mem_Ico (by norm_num) t (-(1/2))
  have hui : |u| ≤ 1/2 := abs_le.mpr ⟨hu.1,by linarith [hu.2]⟩
  let w : ℂ := (r : ℂ)+(u : ℂ)*Complex.I
  have hre : w.re = r := by simp [w]
  have him : w.im = u := by simp [w]
  have hw : w = 0 := (hz w (hre ▸ hrd) (him ▸ hui)).mp (by
    rw [hre,him,← he,ht]; abel)
  have h := congrArg Complex.re hw
  exact hr (by simpa only [hre,Complex.zero_re] using h)

lemma winding_jump {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      γ 0+r • (Complex.I*d) ∉ range γ ∧ γ 0-r • (Complex.I*d) ∉ range γ ∧
      loopIndex (periodicLoop hc 0) (γ 0+r • (Complex.I*d)) -
      loopIndex (periodicLoop hc 0) (γ 0-r • (Complex.I*d)) = 1 := by
  obtain ⟨δ,hδ,hjump⟩ := winding_jump_centred hc hp hinj hd hdn
  obtain ⟨ε,hε,hzero⟩ := transverse_unique_zero_strip hc hp hinj hd hdn
  refine ⟨min δ ε,lt_min hδ hε,?_⟩
  intro r hr hre
  have hn₁ := transverse_displacement_not_mem hp hzero hr.ne'
    (show |r| ≤ ε from (abs_of_pos hr).symm ▸ hre.trans (min_le_right _ _))
  have hn₂ : γ 0-r • (Complex.I*d) ∉ range γ := by
    simpa only [neg_smul,sub_eq_add_neg] using transverse_displacement_not_mem hp hzero
      (neg_ne_zero.mpr hr.ne') (show |-r| ≤ ε by
        rw [abs_neg,abs_of_pos hr]; exact hre.trans (min_le_right _ _))
  refine ⟨hn₁,hn₂,?_⟩
  have hj := hjump r hr (hre.trans (min_le_left _ _))
  change loopIndex (periodicLoop hc (-(1/2))) (γ 0+r • (Complex.I*d))-
    loopIndex (periodicLoop hc (-(1/2))) (γ 0-r • (Complex.I*d)) = 1 at hj
  rwa [loopIndex_periodic_shift hc hp hn₁,loopIndex_periodic_shift hc hp hn₂] at hj

lemma loopIndex_zero_of_re_lt (γ : C(unitInterval,ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, a.re < (γ t).re) : loopIndex γ a = 0 := by
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  have h := HasLogIncrement.of_slit (⟨fun t => γ t-a,by fun_prop⟩ : C(unitInterval,ℂ))
    (fun t => Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr (ha t))))
  simpa only [ContinuousMap.coe_mk,hloop,sub_self,Int.cast_zero,zero_mul] using h

lemma winding_leftmost_normal {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdi : d.im < 0)
    (hmin : ∀ t, (γ 0).re ≤ (γ t).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      γ 0+r • (Complex.I*d) ∉ range γ ∧
      loopIndex (periodicLoop hc 0) (γ 0+r • (Complex.I*d)) = 1 := by
  have hdn : d ≠ 0 := by intro he; simp only [he,Complex.zero_im] at hdi; linarith
  obtain ⟨δ,hδ,hj⟩ := winding_jump hc hp hinj hd hdn
  refine ⟨δ,hδ,?_⟩
  intro r hr hrd
  obtain ⟨hn,_,hjump⟩ := hj r hr hrd
  have hzero : loopIndex (periodicLoop hc 0) (γ 0-r • (Complex.I*d)) = 0 :=
    loopIndex_zero_of_re_lt _ (periodicLoop_closed hc hp 0) (by
      intro t
      change (γ 0-r • (Complex.I*d)).re < (γ ((t:ℝ)+0)).re
      simp only [Complex.sub_re,Complex.smul_re,Complex.mul_re,Complex.I_re,zero_mul,
        Complex.I_im,one_mul,zero_sub,smul_eq_mul]
      nlinarith [hmin ((t:ℝ)+0)])
  rw [hzero,sub_zero] at hjump
  exact ⟨hn,hjump⟩

lemma isMIntegralCurve_iff_hasDerivAt {γ : ℝ → ℂ} {v : ℂ → ℂ} :
    IsMIntegralCurve (I := 𝓘(ℝ,ℂ)) γ v ↔ ∀ t, HasDerivAt γ (v (γ t)) t := by
  constructor
  · intro h t
    have ht : HasFDerivAt γ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (h t)
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using ht.hasDerivAt
  · intro h t
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert (h t).hasFDerivAt using 1
    rfl

lemma exists_global_curve {v : ℂ → ℂ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (x : ℂ) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hv (by simp)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hv.continuous
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hL : ∀ z, ‖v z‖ ≤ (L : ℝ) := fun z => (hB z).trans (le_max_left _ _)
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have he : ∀ z : ℂ, ∃ γ : ℝ → ℂ, γ 0 = z ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ,ℂ)) γ v (Ioo (-1) 1) := by
    intro z
    have hi : IsPicardLindelof (fun _ : ℝ => v)
        (⟨0, by norm_num⟩ : Icc (-1 : ℝ) 1) z L 0 L K := by
      refine ⟨fun _ _ => hK.lipschitzOnWith, fun _ _ => continuousOn_const,
        fun _ _ w _ => hL w, ?_⟩
      simp
    obtain ⟨γ,hγ0,hγ⟩ := hi.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨γ,hγ0,fun t ht => ?_⟩
    exact ((hγ t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨γ,hγ0,hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hm (by norm_num : (0:ℝ)<1) he x
  exact ⟨γ,hγ0,isMIntegralCurve_iff_hasDerivAt.mp hγ⟩

def transverseCoordinate (p : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℝ :=
  (-p Complex.I) • Complex.reCLM + (p 1) • Complex.imCLM

def levelChartDerivative (p : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp p + Complex.I • (Complex.ofRealCLM.comp (transverseCoordinate p))

lemma realFunctional_decomposition (p : ℂ →L[ℝ] ℝ) (w : ℂ) :
    p w = w.re * p 1 + w.im * p Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [hw, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

lemma levelChartDerivative_det (p : ℂ →L[ℝ] ℝ) :
    LinearMap.det (levelChartDerivative p).toLinearMap = (p 1)^2 + (p Complex.I)^2 := by
  rw [determinant_complex_real]
  simp [levelChartDerivative, transverseCoordinate, Complex.mul_re, Complex.mul_im]
  ring

lemma levelChartDerivative_det_pos {p : ℂ →L[ℝ] ℝ} (hp : p ≠ 0) :
    0 < LinearMap.det (levelChartDerivative p).toLinearMap := by
  rw [levelChartDerivative_det]
  have hn : p 1 ≠ 0 ∨ p Complex.I ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext w
    rw [realFunctional_decomposition, h.1, h.2]
    simp
  rcases hn with hn|hn
  · nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (p Complex.I)]
  · nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (p 1)]

lemma exists_regular_level_chart {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧
      (∀ w, (e w).re = f w) ∧
      (∀ w, (e w).im = transverseCoordinate (fderiv ℝ f z) w) := by
  let p := fderiv ℝ f z
  let Φ : ℂ → ℂ := fun w => (f w : ℂ) + Complex.I * (transverseCoordinate p w : ℂ)
  have hc : ContDiffAt ℝ 1 Φ z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hf).add
      (contDiffAt_const.mul ((Complex.ofRealCLM.comp (transverseCoordinate p)).contDiff.contDiffAt))
  have hd : HasFDerivAt Φ (levelChartDerivative p) z := by
    exact (Complex.ofRealCLM.hasFDerivAt.comp z (hf.differentiableAt (by simp)).hasFDerivAt).add
      (((Complex.ofRealCLM.comp (transverseCoordinate p)).hasFDerivAt).const_mul Complex.I)
  let A : ℂ ≃L[ℝ] ℂ := (LinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (ne_of_gt (levelChartDerivative_det_pos hp)))).toContinuousLinearEquiv
  have hA : (A : ℂ →L[ℝ] ℂ) = levelChartDerivative p := by
    ext w
    exact LinearMap.equivOfIsUnitDet_apply _ w
  rw [← hA] at hd
  refine ⟨hc.toOpenPartialHomeomorph Φ hd (by simp),
    hc.mem_toOpenPartialHomeomorph_source hd (by simp), ?_, ?_⟩
  · intro w
    change (Φ w).re = f w
    simp [Φ]
  · intro w
    change (Φ w).im = transverseCoordinate p w
    simp [Φ]

lemma curve_local_level_cover {f : ℂ → ℝ} {γ : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hf : ContDiffAt ℝ 1 f (γ t)) (hp : fderiv ℝ f (γ t) ≠ 0)
    (hγ : ContDiffAt ℝ 1 γ t) (hd : HasDerivAt γ v t) (hv : v ≠ 0)
    (hc : ∀ s, f (γ s) = f (γ t)) {U : Set ℝ} (hU : U ∈ 𝓝 t) :
    ∀ᶠ w in 𝓝 (γ t), f w = f (γ t) → w ∈ γ '' U := by
  let p := fderiv ℝ f (γ t)
  let q := transverseCoordinate p
  have hfd := (hf.differentiableAt (by simp)).hasFDerivAt
  have hpv : p v = 0 := by
    have hh := hfd.comp_hasDerivAt t hd
    have he : (f ∘ γ) = fun _ => f (γ t) := funext hc
    rw [he] at hh
    exact hh.unique (hasDerivAt_const t _)
  have hqv : q v ≠ 0 := by
    intro hq
    have hA : IsUnit (LinearMap.det (levelChartDerivative p).toLinearMap) :=
      isUnit_iff_ne_zero.mpr (ne_of_gt (levelChartDerivative_det_pos hp))
    let A := LinearMap.equivOfIsUnitDet hA
    have hz : A v = A 0 := by
      rw [show A v = levelChartDerivative p v from LinearMap.equivOfIsUnitDet_apply _ v,
        show A 0 = levelChartDerivative p 0 from LinearMap.equivOfIsUnitDet_apply _ 0]
      simp [levelChartDerivative, hpv, show transverseCoordinate p v = 0 from hq]
    exact hv (A.injective hz)
  let ψ : ℝ → ℝ := fun s => q (γ s)
  have hψ : HasStrictDerivAt ψ (q v) t :=
    (q.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (q.hasFDerivAt.comp_hasDerivAt t hd) (by simp)
  let σ := hψ.localInverse ψ (q v) t hqv
  have hσ : σ (ψ t) = t := hψ.eventually_left_inverse hqv |>.self_of_nhds
  have hσc : Tendsto σ (𝓝 (ψ t)) (𝓝 t) := by
    have ht : Tendsto σ (𝓝 (ψ t)) (𝓝 (σ (ψ t))) :=
      (hψ.to_localInverse hqv).hasDerivAt.continuousAt.tendsto
    rwa [hσ] at ht
  obtain ⟨e,het,her,hei⟩ := exists_regular_level_chart hf hp
  have hw : ∀ᶠ w in 𝓝 (γ t), w ∈ e.source := e.open_source.mem_nhds het
  have hqc : Tendsto q (𝓝 (γ t)) (𝓝 (ψ t)) := q.continuous.continuousAt.tendsto
  have hi : ∀ᶠ w in 𝓝 (γ t), ψ (σ (q w)) = q w :=
    hqc.eventually (hψ.eventually_right_inverse hqv)
  have hu : ∀ᶠ w in 𝓝 (γ t), σ (q w) ∈ U := (hσc.comp hqc).eventually hU
  have hs : ∀ᶠ w in 𝓝 (γ t), γ (σ (q w)) ∈ e.source :=
    (hγ.continuousAt.tendsto.comp (hσc.comp hqc)).eventually hw
  filter_upwards [hw,hi,hu,hs] with w hw hi hu hs hfwe
  refine ⟨σ (q w),hu, e.injOn hs hw ?_⟩
  apply Complex.ext
  · rw [her,her,hc,hfwe]
  · rw [hei,hei]
    exact hi

lemma integral_curve_contDiff_one {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : Continuous v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) :
    ContDiff ℝ 1 γ := by
  apply contDiff_one_iff_deriv.mpr
  have hc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  refine ⟨fun t => (hγ t).differentiableAt, ?_⟩
  have he : deriv γ = v ∘ γ := funext fun t => (hγ t).deriv
  rw [he]
  exact hv.comp hc

lemma integral_curve_first_integral {f : ℂ → ℝ} {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hf : Differentiable ℝ f) (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (s t : ℝ) : f (γ s) = f (γ t) := by
  have hd (t : ℝ) : HasDerivAt (fun t => f (γ t)) 0 t := by
    convert (hf (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t) using 1 <;>
      first | rfl | simp only [horth]
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

lemma integral_curves_shift_eq {v : ℂ → ℂ} {γ κ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hκ : ∀ t, HasDerivAt κ (v (κ t)) t)
    {a b : ℝ} (he : γ a = κ b) (s : ℝ) : γ (s+a) = κ (s+b) := by
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hh := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hm
    ((isMIntegralCurve_iff_hasDerivAt.mpr hγ).comp_add a)
    ((isMIntegralCurve_iff_hasDerivAt.mpr hκ).comp_add b) (by simpa using he)
  exact congrFun hh s

lemma curve_isOpenMap_level {f : ℂ → ℝ} {γ : ℝ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hγ : ContDiff ℝ 1 γ) (hn : ∀ t, deriv γ t ≠ 0)
    (hc : ∀ t, f (γ t) = c) :
    IsOpenMap (fun t => (⟨γ t,hc t⟩ : {z : ℂ | f z = c})) := by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨t,ht,rfl⟩
  have hh := curve_local_level_cover hf.contDiffAt (hp _ (hc t)) hγ.contDiffAt
    (hγ.differentiable (by simp) t).hasDerivAt (hn t)
    (fun s => (hc s).trans (hc t).symm) (hU.mem_nhds ht)
  have hm : Tendsto (Subtype.val : {z : ℂ | f z = c} → ℂ)
      (𝓝 ⟨γ t,hc t⟩) (𝓝 (γ t)) := continuous_subtype_val.continuousAt.tendsto
  have he := hm.eventually hh
  filter_upwards [he] with w hw
  obtain ⟨s,hs,heq⟩ := hw (w.property.trans (hc t).symm)
  exact ⟨s,hs,Subtype.ext heq⟩

lemma compact_regular_level_periodic {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    (hK : IsCompact {z : ℂ | f z = c}) {γ : ℝ → ℂ}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (hγ0 : f (γ 0) = c) :
    ∃ T > 0, Periodic γ T := by
  let K := {z : ℂ | f z = c}
  have hc (t : ℝ) : f (γ t) = c :=
    (integral_curve_first_integral (hf.differentiable (by simp)) horth hγ t 0).trans hγ0
  let Γ : ℝ → K := fun t => ⟨γ t,hc t⟩
  have hγc := integral_curve_contDiff_one hv.continuous hγ
  have hΓo : IsOpenMap Γ := curve_isOpenMap_level hf hp hγc
    (fun t => by rw [(hγ t).deriv]; exact hn _ (hc t)) hc
  have hΓc : Continuous Γ := hγc.continuous.subtype_mk _
  have hclosed : IsClosed (range Γ) := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    obtain ⟨κ,hκ0,hκ⟩ := exists_global_curve hv hvc w.val
    have hκc (s : ℝ) : f (κ s) = c := by
      rw [integral_curve_first_integral (hf.differentiable (by simp)) horth hκ s 0, hκ0]
      exact w.property
    let Δ : ℝ → K := fun s => ⟨κ s,hκc s⟩
    have hΔo : IsOpenMap Δ := curve_isOpenMap_level hf hp
      (integral_curve_contDiff_one hv.continuous hκ)
      (fun s => by rw [(hκ s).deriv]; exact hn _ (hκc s)) hκc
    have hwΔ : w ∈ range Δ := ⟨0,Subtype.ext hκ0⟩
    apply mem_of_superset (hΔo.isOpen_range.mem_nhds hwΔ)
    rintro y ⟨s,rfl⟩ ⟨t,ht⟩
    apply hw
    have he : γ t = κ s := congrArg Subtype.val ht
    refine ⟨-s+t,Subtype.ext ?_⟩
    have hh := integral_curves_shift_eq hv hγ hκ he (-s)
    simpa only [neg_add_cancel,hκ0] using hh
  have hcompact : IsCompact (range Γ) := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact hclosed.isCompact
  have hnotinj : ¬ Injective γ := by
    intro hi
    have hΓi : Injective Γ := fun a b h => hi (congrArg Subtype.val h)
    have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hΓc hΓi hΓo
    apply noncompact_univ ℝ
    apply he.isEmbedding.isCompact_iff.mpr
    simpa only [image_univ] using hcompact
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  exact (xor_iff_iff_not.mp
    ((isMIntegralCurve_iff_hasDerivAt.mpr hγ).periodic_xor_injective hm)).mpr hnotinj

lemma curve_locally_injective {γ : ℝ → ℂ} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 γ t) (hn : deriv γ t ≠ 0) :
    ∃ ε > 0, InjOn γ (Metric.ball t ε) := by
  obtain ⟨p,hp⟩ : ∃ p : ℂ →L[ℝ] ℝ, p (deriv γ t) ≠ 0 := by
    by_cases hr : (deriv γ t).re = 0
    · refine ⟨Complex.imCLM,fun hi => hn (Complex.ext hr hi)⟩
    · exact ⟨Complex.reCLM,hr⟩
  have hd : HasStrictDerivAt (fun s => p (γ s)) (p (deriv γ t)) t :=
    (p.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (p.hasFDerivAt.comp_hasDerivAt t
        (hγ.differentiableAt (by simp)).hasDerivAt) (by simp)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (hd.eventually_left_inverse hp)
  refine ⟨ε,hε,fun a ha b hb he => ?_⟩
  have h₁ := hsub ha
  have h₂ := hsub hb
  change HasStrictDerivAt.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hd hp (p (γ a)) = a at h₁
  change HasStrictDerivAt.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hd hp (p (γ b)) = b at h₂
  rw [he] at h₁
  exact h₁.symm.trans h₂

lemma integral_curve_simple_period {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hn : v (γ 0) ≠ 0) (hper : ∃ T > 0, Periodic γ T) :
    ∃ T > 0, Periodic γ T ∧ InjOn γ (Ico 0 T) := by
  have hγc := integral_curve_contDiff_one hv.continuous hγ
  obtain ⟨ε,hε,hεinj⟩ := curve_locally_injective (t := 0) hγc.contDiffAt
    (by rw [(hγ 0).deriv]; exact hn)
  have hlow : ∀ t, 0 < t → γ t = γ 0 → ε ≤ t := by
    intro t ht he
    by_contra hh
    have hlt : t < ε := lt_of_not_ge hh
    have hmem : t ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hlt
    have hz := hεinj hmem (Metric.mem_ball_self hε) he
    linarith
  obtain ⟨T,hT,hpT⟩ := hper
  have hTr : γ T = γ 0 := by simpa using hpT 0
  let S := Icc ε T ∩ {t | γ t = γ 0}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_eq hγc.continuous continuous_const)
  obtain ⟨P,hP,hmin⟩ := hS.exists_isMinOn ⟨T,⟨⟨hlow T hT hTr,le_rfl⟩,hTr⟩⟩
    continuousOn_id
  have hPpos : 0 < P := hε.trans_le hP.1.1
  have hleast : ∀ t, 0 < t → γ t = γ 0 → P ≤ t := by
    intro t ht he
    by_cases hle : t ≤ T
    · exact hmin ⟨⟨hlow t ht he,hle⟩,he⟩
    · exact hP.1.2.trans (le_of_not_ge hle)
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hi := isMIntegralCurve_iff_hasDerivAt.mpr hγ
  have hPP : Periodic γ P := by simpa using hi.periodic_of_eq hm hP.2
  refine ⟨P,hPpos,hPP,fun a ha b hb he => ?_⟩
  rcases lt_trichotomy a b with hab|hab|hab
  · have hper := hi.periodic_of_eq hm he.symm
    have hret : γ (b-a) = γ 0 := by simpa using hper 0
    have hh := hleast (b-a) (sub_pos.mpr hab) hret
    linarith [ha.1,hb.2]
  · exact hab
  · have hper := hi.periodic_of_eq hm he
    have hret : γ (a-b) = γ 0 := by simpa using hper 0
    have hh := hleast (a-b) (sub_pos.mpr hab) hret
    linarith [hb.1,ha.2]

lemma integral_curves_range_eq {v : ℂ → ℂ} {γ κ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hκ : ∀ t, HasDerivAt κ (v (κ t)) t)
    {a b : ℝ} (he : γ a = κ b) : range γ = range κ := by
  apply Subset.antisymm
  · rintro _ ⟨s,rfl⟩
    refine ⟨s-a+b, ?_⟩
    have hh := integral_curves_shift_eq hv hγ hκ he (s-a)
    simpa only [sub_add_cancel] using hh.symm
  · rintro _ ⟨s,rfl⟩
    refine ⟨s-b+a, ?_⟩
    have hh := integral_curves_shift_eq hv hκ hγ he.symm (s-b)
    simpa only [sub_add_cancel] using hh.symm

lemma compact_regular_level_finite_curves {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    (hK : IsCompact {z : ℂ | f z = c}) :
    ∃ C : Finset (Set ℂ), (⋃ S ∈ C, S) = {z : ℂ | f z = c} ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C, ∃ γ : ℝ → ℂ, ∃ P > 0,
        range γ = S ∧ (∀ t, HasDerivAt γ (v (γ t)) t) ∧
        Periodic γ P ∧ InjOn γ (Ico 0 P) := by
  classical
  let K := {z : ℂ | f z = c}
  have hE : ∀ z : K, ∃ γ : ℝ → ℂ, γ 0 = z.val ∧
      ∀ t, HasDerivAt γ (v (γ t)) t := fun z => exists_global_curve hv hvc z.val
  choose γ hγ0 hγ using hE
  have hc (z : K) (t : ℝ) : f (γ z t) = c := by
    rw [integral_curve_first_integral (hf.differentiable (by simp)) horth (hγ z) t 0,
      hγ0 z]
    exact z.property
  let Γ (z : K) : ℝ → K := fun t => ⟨γ z t,hc z t⟩
  have hΓo (z : K) : IsOpenMap (Γ z) := curve_isOpenMap_level hf hp
    (integral_curve_contDiff_one hv.continuous (hγ z))
    (fun t => by rw [(hγ z t).deriv]; exact hn _ (hc z t)) (hc z)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun z : K => range (Γ z))
    (fun z => (hΓo z).isOpen_range) (by
      intro z _
      exact mem_iUnion.mpr ⟨z,0,Subtype.ext (hγ0 z)⟩)
  let C := s.image (fun z => range (γ z))
  refine ⟨C,?_,?_,?_⟩
  · ext w
    constructor
    · intro hw
      obtain ⟨S,hS,hw⟩ := mem_iUnion₂.mp hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨t,rfl⟩ := hw
      exact hc z t
    · intro hw
      obtain ⟨z,hz,t,ht⟩ := mem_iUnion₂.mp (hs (mem_univ (⟨w,hw⟩ : K)))
      refine mem_iUnion₂.mpr ⟨range (γ z),Finset.mem_image.mpr ⟨z,hz,rfl⟩,t,?_⟩
      exact congrArg Subtype.val ht
  · intro S hS T hT hne
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hT
    apply disjoint_left.mpr
    rintro a ⟨s,hs⟩ ⟨t,ht⟩
    exact hne (integral_curves_range_eq hv (hγ z) (hγ w) (hs.trans ht.symm))
  · intro S hS
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨P,hP,hper,hinj⟩ := integral_curve_simple_period hv (hγ z)
      (hn _ (hc z 0))
      (compact_regular_level_periodic hf hv hvc horth hp hn hK (hγ z) (hc z 0))
    exact ⟨γ z,P,hP,rfl,hγ z,hper,hinj⟩

lemma integral_curve_contDiff_two {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) :
    ContDiff ℝ 2 γ := by
  have hc := integral_curve_contDiff_one hv.continuous hγ
  rw [show (2 : WithTop ℕ∞) = 1+1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (hγ t).differentiableAt, by simp, ?_⟩
  have he : deriv γ = v ∘ γ := funext (fun t => (hγ t).deriv)
  rw [he]
  exact hv.comp hc

end Brennan

end

end OAI
