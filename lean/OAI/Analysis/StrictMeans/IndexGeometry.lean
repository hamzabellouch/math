import OAI.Analysis.StrictMeans.GenericTargets

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma nonsingular_locally_injective {G : ℂ → ℂ} {z : ℂ}
    (hG : ContDiffAt ℝ 1 G z) (hdet : (fderiv ℝ G z).det ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ InjOn G U := by
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfDetNeZero (fderiv ℝ G z).toLinearMap hdet).toContinuousLinearEquiv
  have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ G z := by
    ext w
    simp [e, LinearMap.equivOfDetNeZero, LinearEquiv.ofIsUnitDet_apply]
  have hs : HasStrictFDerivAt G (e : ℂ →L[ℝ] ℂ) z := by
    rw [he]
    exact hG.hasStrictFDerivAt one_ne_zero
  let E := hs.toOpenPartialHomeomorph G
  exact ⟨E.source, E.open_source, hs.mem_toOpenPartialHomeomorph_source, E.injOn⟩

lemma compact_level_regular_fiber_finite {G : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hG : ContinuousOn G K) (ξ : ℂ)
    (hregular : ∀ z ∈ K, G z = ξ → ContDiffAt ℝ 1 G z ∧ (fderiv ℝ G z).det ≠ 0) :
    (K ∩ G ⁻¹' {ξ}).Finite := by
  let S := K ∩ G ⁻¹' {ξ}
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosed {x : K | G x = ξ} :=
    isClosed_eq hG.domRestrict continuous_const
  have hc : IsCompact S := by
    convert hclosed.isCompact.image continuous_subtype_val using 1
    ext x
    simp only [S, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, mem_ofPred_eq,
      Subtype.exists, exists_and_right, exists_eq_right]
    tauto
  have : DiscreteTopology S := discreteTopology_subtype_iff'.mpr (by
    intro z hz
    obtain ⟨ho, hd⟩ := hregular z hz.1 hz.2
    obtain ⟨U, hU, hzU, hi⟩ := nonsingular_locally_injective ho hd
    refine ⟨U, hU, ?_⟩
    ext w
    constructor
    · intro hw
      exact mem_singleton_iff.mpr (hi hw.1 hzU (hw.2.2.trans hz.2.symm))
    · rintro rfl
      exact ⟨hzU, hz⟩)
  have : CompactSpace S := isCompact_iff_compactSpace.mp hc
  have : Finite S := finite_of_compact_of_discrete
  exact Set.toFinite S

def criticalCut (k : ℝ) (f : DiskFamily) (ξ : ℂ) (h : ℝ) : Set UpperHalfPlane :=
  {z | criticalMap k (halfPlaneFunction f) z = ξ ∧ h ≤ criticalHeight k (halfPlaneFunction f) z}

lemma goodPair_criticalCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0 < h) : (criticalCut k f ξ h).Finite := by
  let K := potentialSuperlevel k (halfPlaneFunction f) ξ h
  have hcont : ContinuousOn (criticalMap k (halfPlaneFunction f)) K := by
    intro z hz
    exact (criticalMap_contDiffAt k f hz.1).continuousAt.continuousWithinAt
  have hf := compact_level_regular_fiber_finite (hg.1 h hh) hcont ξ (by
    intro z hz he
    refine ⟨(criticalMap_contDiffAt k f hz.1).of_le (by norm_num), ?_⟩
    exact (not_congr (jacobianExpression_zero_iff k hk.ne' f hz.1)).mp
      (hg.2.1 ⟨z,hz.1⟩ he))
  have hs : criticalCut k f ξ h ⊆ (fun z : UpperHalfPlane => (z:ℂ)) ⁻¹' (K ∩ criticalMap k (halfPlaneFunction f) ⁻¹' {ξ}) := by
    intro z hz
    exact ⟨(criticalHeight_superlevel hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos) hh hz.1).mpr hz.2,hz.1⟩
  exact (hf.preimage UpperHalfPlane.coe_injective.injOn).subset hs

def maximaCut (k : ℝ) (f : DiskFamily) (ξ : ℂ) (h : ℝ) : Set UpperHalfPlane :=
  {z ∈ criticalCut k f ξ h | jacobianExpression k (halfPlaneFunction f) z < 0}

def saddleCut (k : ℝ) (f : DiskFamily) (ξ : ℂ) (h : ℝ) : Set UpperHalfPlane :=
  {z ∈ criticalCut k f ξ h | 0 < jacobianExpression k (halfPlaneFunction f) z}

lemma maximaCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0 < h) : (maximaCut k f ξ h).Finite :=
  (goodPair_criticalCut_finite hk hg hh).subset (fun _ hz => hz.1)

lemma saddleCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0 < h) : (saddleCut k f ξ h).Finite :=
  (goodPair_criticalCut_finite hk hg hh).subset (fun _ hz => hz.1)

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

def realHessian (u : ℂ → ℝ) (z v w : ℂ) : ℝ :=
  fderiv ℝ (fun t => fderiv ℝ u t w) z v

lemma logPotential_hessian {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) (v w : ℂ) :
    realHessian (logPotential k F ξ) z v w =
      -(k / z.im^2) * v.im * w.im -
        ((((deriv (deriv F) z * (F z-ξ) - deriv F z * deriv F z) / (F z-ξ)^2) * v) * w).re := by
  let r := fun t => deriv F t / (F t-ξ)
  have hdr : HasDerivAt r
      ((deriv (deriv F) z * (F z-ξ) - deriv F z * deriv F z) / (F z-ξ)^2) z := by
    exact (hF.deriv.differentiableAt.hasDerivAt).div
      (hF.differentiableAt.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)
  have hy := ((hasDerivAt_const z.im k).div (hasDerivAt_id z.im) hz.ne')
  have h1 := (hy.comp_hasFDerivAt z (Complex.imCLM.hasFDerivAt (x := z))).mul_const w.im
  have h2 := (Complex.reCLM.hasFDerivAt (x := r z * w)).comp z
    (hdr.complexToReal_fderiv.mul_const w)
  have he : (fun t => fderiv ℝ (logPotential k F ξ) t w) =ᶠ[𝓝 z]
      (fun t => k / t.im * w.im - (r t*w).re) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hF.eventually_analyticAt,
      hF.continuousAt.eventually_ne hp] with t ht hFt hpt
    exact logPotential_fderiv_apply ht hFt.differentiableAt hpt w
  have hh := (h1.sub h2).congr_of_eventuallyEq he
  unfold realHessian
  rw [hh.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
    Complex.imCLM_apply, Complex.reCLM_apply, one_apply_eq_self, id_eq]
  ring_nf

lemma logPotential_hessian_trace {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    realHessian (logPotential k F ξ) z 1 1 + realHessian (logPotential k F ξ) z I I =
      -k / z.im^2 := by
  rw [logPotential_hessian hz hF hp, logPotential_hessian hz hF hp]
  simp only [one_im, I_im, mul_zero, zero_sub, mul_one, Complex.mul_I_re, Complex.mul_I_im]
  ring

lemma critical_logarithmic_quotient_deriv {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hd : deriv F z ≠ 0)
    (hg : criticalMap k F z = ξ) :
    (deriv (deriv F) z * (F z-ξ) - deriv F z * deriv F z) / (F z-ξ)^2 =
      (k:ℂ) * ((k:ℂ) + logarithmicDerivative F z) / (z.im:ℂ)^2 := by
  rw [criticalMap_sub_image hg]
  unfold logarithmicDerivative
  field_simp [Complex.ofReal_ne_zero.mpr hk, Complex.ofReal_ne_zero.mpr hz.ne',hd]
  simp only [I_sq]
  ring

lemma logPotential_critical_hessian {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hd : deriv F z ≠ 0)
    (hg : criticalMap k F z = ξ) :
    realHessian (logPotential k F ξ) z 1 1 =
        k / z.im^2 * (-(k+(logarithmicDerivative F z).re)) ∧
    realHessian (logPotential k F ξ) z 1 I =
        k / z.im^2 * (logarithmicDerivative F z).im ∧
    realHessian (logPotential k F ξ) z I 1 =
        k / z.im^2 * (logarithmicDerivative F z).im ∧
    realHessian (logPotential k F ξ) z I I =
        k / z.im^2 * (k-1+(logarithmicDerivative F z).re) := by
  have hp : F z ≠ ξ := fun he => criticalMap_ne_image hk hz hd (hg.trans he.symm)
  have hq := critical_logarithmic_quotient_deriv hk hz hd hg
  repeat' apply And.intro
  all_goals rw [logPotential_hessian hz hF hp,hq]
  all_goals simp only [one_im, I_im, I_re, mul_zero, zero_sub, mul_one, Complex.div_ofReal_re, Complex.div_ofReal_im,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, zero_mul, add_zero, sub_zero]
  all_goals ring

lemma logPotential_hessian_det {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hd : deriv F z ≠ 0)
    (hg : criticalMap k F z = ξ) :
    realHessian (logPotential k F ξ) z 1 1 * realHessian (logPotential k F ξ) z I I -
      realHessian (logPotential k F ξ) z 1 I * realHessian (logPotential k F ξ) z I 1 =
        -(k^4 / z.im^4) * jacobianExpression k F z := by
  obtain ⟨hxx,hxy,hyx,hyy⟩ := logPotential_critical_hessian hk hz hF hd hg
  rw [hxx,hxy,hyx,hyy]
  unfold jacobianExpression
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  field_simp
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma log_tangent_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y - Real.log x ≤ (y-x)/x := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hh
  convert hh using 1
  field_simp

lemma log_tangent_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : y ≠ x) :
    Real.log y - Real.log x < (y-x)/x := by
  have hh := Real.log_lt_sub_one_of_pos (div_pos hy hx)
    (show y/x ≠ 1 from fun he => hne ((div_eq_one_iff_eq hx.ne').mp he))
  rw [Real.log_div hy.ne' hx.ne'] at hh
  convert hh using 1
  field_simp

lemma logPotential_not_isLocalMin {k : ℝ} (hk : 0 < k) {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    ¬ IsLocalMin (logPotential k F ξ) z := by
  intro hm
  let c : ℝ := k / z.im
  let H : ℂ → ℂ := fun w => (F w-ξ)*Complex.exp ((c:ℂ)*I*(w-z))
  have he (w : ℂ) : (((c:ℂ)*I*(w-z)):ℂ).re = -c*(w.im-z.im) := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.sub_im,mul_zero,zero_sub,mul_one,add_zero]
    ring
  have hlog (w : ℂ) (hw : F w ≠ ξ) :
      Real.log ‖H w‖ = Real.log ‖F w-ξ‖ - c*(w.im-z.im) := by
    dsimp [H]
    rw [norm_mul,Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))
      (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)),Complex.norm_exp,Real.log_exp,he]
    ring
  have hHd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ H w := by
    filter_upwards [hF.eventually_analyticAt] with w hw
    dsimp [H]
    exact (hw.differentiableAt.sub_const ξ).mul
      (Complex.differentiable_exp.differentiableAt.comp w
        (by fun_prop : DifferentiableAt ℂ (fun w => (c:ℂ)*I*(w-z)) w))
  have hHn (w : ℂ) (hw : F w ≠ ξ) : 0 < ‖H w‖ := by
    dsimp [H]
    exact norm_pos_iff.mpr (mul_ne_zero (sub_ne_zero.mpr hw) (Complex.exp_ne_zero _))
  have hmax : IsLocalMax (norm ∘ H) z := by
    filter_upwards [hm,isOpen_halfPlane.mem_nhds hz,hF.continuousAt.eventually_ne hp] with w hmw hwy hpw
    change ‖H w‖ ≤ ‖H z‖
    rw [← Real.log_le_log_iff (hHn w hpw) (hHn z hp),hlog w hpw,hlog z hp]
    have ht := mul_le_mul_of_nonneg_left (log_tangent_bound hz hwy) hk.le
    change k*Real.log z.im - Real.log ‖F z-ξ‖ ≤ k*Real.log w.im - Real.log ‖F w-ξ‖ at hmw
    have hc : k*((w.im-z.im)/z.im) = c*(w.im-z.im) := by dsimp [c]; ring
    rw [hc] at ht
    linarith
  have hce := Complex.norm_eventually_eq_of_isLocalMax hHd hmax
  have hpath : Tendsto (fun t : ℝ => z+(t:ℂ)*I) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z+(t:ℂ)*I) := by fun_prop
    simpa using hc.tendsto (0:ℝ)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
      logPotential k F ξ z ≤ logPotential k F ξ (z+(t:ℂ)*I) ∧
      ‖H (z+(t:ℂ)*I)‖ = ‖H z‖ ∧
      F (z+(t:ℂ)*I) ≠ ξ ∧ 0 < t := by
    filter_upwards [(hpath.eventually hm).filter_mono nhdsWithin_le_nhds,
      (hpath.eventually hce).filter_mono nhdsWithin_le_nhds,
      (hpath.eventually (hF.continuousAt.eventually_ne hp)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hm' hce' hp' ht
    exact ⟨hm',hce',hp',ht⟩
  obtain ⟨t,hmt,het,hpt,ht⟩ := hev.exists
  have hym : (z+(t:ℂ)*I).im = z.im+t := by simp
  have hypos : 0 < (z+(t:ℂ)*I).im := by rw [hym]; linarith
  have hyne : (z+(t:ℂ)*I).im ≠ z.im := by rw [hym]; linarith
  have hlogs := congrArg Real.log het
  rw [hlog _ hpt,hlog z hp] at hlogs
  have hstrict := mul_lt_mul_of_pos_left (log_tangent_strict hz hypos hyne) hk
  have hc : k*(((z+(t:ℂ)*I).im-z.im)/z.im) =
      c*((z+(t:ℂ)*I).im-z.im) := by dsimp [c]; ring
  rw [hc] at hstrict
  change k*Real.log z.im - Real.log ‖F z-ξ‖ ≤
    k*Real.log (z+(t:ℂ)*I).im - Real.log ‖F (z+(t:ℂ)*I)-ξ‖ at hmt
  linarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma compact_strict_maximum_principle {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {u : X → ℝ} (hu : ContinuousOn u K) {c : ℝ}
    (hbd : ∀ z ∈ frontier K, u z ≤ c)
    (hlocal : ∀ z ∈ interior K, c ≤ u z → ¬ IsLocalMax u z) :
    ∀ z ∈ interior K, u z < c := by
  intro z hz
  by_contra hzc
  have hzc' : c ≤ u z := le_of_not_gt hzc
  obtain ⟨w,hw,hm⟩ := hK.exists_isMaxOn ⟨z,interior_subset hz⟩ hu
  by_cases hwi : w ∈ interior K
  · exact hlocal w hwi (hzc'.trans (hm (interior_subset hz)))
      (hm.isLocalMax (mem_interior_iff_mem_nhds.mp hwi))
  · have hwbd : w ∈ frontier K := by
      rw [hK.isClosed.frontier_eq]
      exact ⟨hw,hwi⟩
    have hwc := hbd w hwbd
    have he : u z = u w := le_antisymm (hm (interior_subset hz)) (hwc.trans hzc')
    exact hlocal z hz hzc' (show IsLocalMax u z from Filter.Eventually.filter_mono
      (le_principal_iff.mpr (mem_interior_iff_mem_nhds.mp hz)) (show ∀ᶠ v in 𝓟 K, u v ≤ u z from by
        filter_upwards [hm] with v hv
        exact hv.trans he.ge))

lemma reciprocal_logPotential_not_isLocalMax {k : ℝ} (hk : 0 < k)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0 < z.im) (hF : AnalyticAt ℂ F z)
    (hp : F z ≠ ξ) :
    ¬ IsLocalMax (fun w : ℂ => ‖F w-ξ‖ / w.im^k) z := by
  intro hm
  apply logPotential_not_isLocalMin hk hz hF hp
  filter_upwards [hm,isOpen_halfPlane.mem_nhds hz,hF.continuousAt.eventually_ne hp] with w hw hwy hpw
  have hn (v : ℂ) (hy : 0 < v.im) (hv : F v ≠ ξ) : 0 < ‖F v-ξ‖ / v.im^k :=
    div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv)) (Real.rpow_pos_of_pos hy k)
  have he (v : ℂ) (hy : 0 < v.im) (hv : F v ≠ ξ) :
      Real.log (‖F v-ξ‖ / v.im^k) = -logPotential k F ξ v := by
    rw [Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hv))
      (Real.rpow_pos_of_pos hy k).ne',Real.log_rpow hy]
    unfold logPotential
    ring
  have hh := Real.log_le_log (hn w hwy hpw) hw
  rw [he w hwy hpw,he z hz hp] at hh
  exact neg_le_neg_iff.mp hh

lemma reciprocal_potential_inside_boundary {k : ℝ} (hk : 0 < k)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im})
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F K) (ξ : ℂ) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ z ∈ frontier K, ‖F z-ξ‖ / z.im^k ≤ c) :
    ∀ z ∈ interior K, ‖F z-ξ‖ / z.im^k < c := by
  apply compact_strict_maximum_principle hK
    ((hF.continuousOn.sub continuousOn_const).norm.div
      (Complex.continuous_im.continuousOn.rpow_const (fun z hz => Or.inl (ne_of_gt (show 0 < z.im from hKH hz))))
      (fun z hz => (Real.rpow_pos_of_pos (show 0 < z.im from hKH hz) k).ne')) hbd
  intro z hz hzc
  change c ≤ ‖F z-ξ‖ / z.im^k at hzc
  have hzK := interior_subset hz
  have hp : F z ≠ ξ := by
    intro he
    have hzv : ‖F z-ξ‖ / z.im^k = 0 := by rw [he,sub_self,norm_zero,zero_div]
    rw [hzv] at hzc
    exact (not_le_of_gt hc) hzc
  exact reciprocal_logPotential_not_isLocalMax hk (hKH hzK) (hF z hzK) hp

end
end StrictInverseFirstPower

end

end OAI
