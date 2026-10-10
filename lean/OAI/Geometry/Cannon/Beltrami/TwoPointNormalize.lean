import Mathlib
import OAI.Geometry.Cannon.Beltrami.CauchySymbol

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

namespace CannonBeltrami

lemma hasCompactSupport_partialZ {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (partialZ f) := by
  apply hf.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ (isClosed_tsupport f))
  intro z hz
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hn
  exact hz (by simp [partialZ,hd])

lemma smoothBeurling_decay (f : SchwartzMap ℂ ℂ) :
    Tendsto (smoothBeurling f) (cocompact ℂ) (𝓝 0) := by
  have ht : Tendsto (𝓕 (fun z => beurlingSymbol z*(𝓕 f) z)) (cocompact ℂ) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact _
  have he : smoothBeurling f=(fun z => (𝓕 (fun w => beurlingSymbol w*(𝓕 f) w)) (-z)) := by
    funext z
    rw [smoothBeurling_fourier,Real.fourierInv_eq_fourier_neg]
  rw [he]
  exact ht.comp (Homeomorph.neg ℂ).toCocompactMap.cocompact_tendsto'

lemma smoothBeurling_compatibility (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    partialBar (smoothBeurling f) z=partialZ f z := by
  have hbar : partialBar (cauchyTransform f)=f := funext (fun z => (cauchyTransform_partials f z).1)
  have hz : partialZ (cauchyTransform f)=smoothBeurling f :=
    funext (fun z => (cauchyTransform_partials f z).2)
  rw [← hz,wirtinger_commute (contDiff_cauchyTransform f),hbar]

theorem smooth_nonvanishing_factor (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ (h : SchwartzMap ℂ ℂ) (q : ℂ → ℂ), HasCompactSupport (h : ℂ → ℂ) ∧
      ContDiff ℝ ∞ q ∧ (∀ z, q z ≠ 0) ∧
      (∀ z, h z=μ z*q z) ∧ (∀ z, 1+smoothBeurling h z=q z) := by
  have hμ : ContDiff ℝ ∞ (μ : ℂ → ℂ) := μ.smooth ⊤
  let b : SchwartzMap ℂ ℂ := (hasCompactSupport_partialZ hcμ).toSchwartzMap (contDiff_partials hμ).1
  obtain ⟨w,hcw,hw⟩ := solve_compact_smooth_beltrami μ b hcμ
    (hasCompactSupport_partialZ hcμ) hk hk1 hb
  let q : ℂ → ℂ := fun z => Complex.exp (cauchyTransform w z)
  have hq : ContDiff ℝ ∞ q := (contDiff_cauchyTransform w).cexp
  have hc : HasCompactSupport (fun z => μ z*q z) := hcμ.mul_right
  let h : SchwartzMap ℂ ℂ := hc.toSchwartzMap (hμ.mul hq)
  refine ⟨h,q,hc,hq,fun z => Complex.exp_ne_zero _,fun z => rfl,?_⟩
  let g : ℂ → ℂ := fun z => q z-1-smoothBeurling h z
  have hg : ContDiff ℝ ∞ g := (hq.sub contDiff_const).sub (contDiff_smoothBeurling h)
  have hgz (z : ℂ) : partialBar g z=0 := by
    have hdq : DifferentiableAt ℝ q z := hq.differentiable (by simp) z
    have hdμ : DifferentiableAt ℝ (μ : ℂ → ℂ) z := hμ.differentiable (by simp) z
    have hdC : DifferentiableAt ℝ (cauchyTransform w) z :=
      (contDiff_cauchyTransform w).differentiable (by simp) z
    have hbq : partialBar q z=q z*w z := by
      rw [partials_exp hdC |>.2,(cauchyTransform_partials w z).1]
    have hpq : partialZ q z=q z*smoothBeurling w z := by
      rw [partials_exp hdC |>.1,(cauchyTransform_partials w z).2]
    have hwp : w z-μ z*smoothBeurling w z=partialZ μ z := hw z
    have hph : partialZ h z=partialZ μ z*q z+μ z*partialZ q z :=
      (partials_mul hdμ hdq).1
    change partialBar (fun z => (q z-1)-smoothBeurling h z) z=0
    rw [(partials_sub (f:=fun z => q z-1) (g:=smoothBeurling h) (hdq.sub (differentiableAt_const 1))
      ((contDiff_smoothBeurling h).differentiable (by simp) z)).2]
    rw [(partials_sub (g:=fun _ => (1:ℂ)) hdq (differentiableAt_const 1)).2,(partials_const 1 z).2,
      smoothBeurling_compatibility,hph,hbq,hpq]
    linear_combination q z*hwp
  have hqt : Tendsto q (cocompact ℂ) (𝓝 1) := by
    simpa [q, Function.comp_def] using Complex.continuous_exp.continuousAt.tendsto.comp (cauchyTransform_zero_at_infty w)
  have hgt : Tendsto g (cocompact ℂ) (𝓝 0) := by
    simpa [g] using (hqt.sub (tendsto_const_nhds (x:=(1:ℂ)))).sub (smoothBeurling_decay h)
  intro z
  have he := liouville_partialBar (hg.differentiable (by simp)) hgz hgt z
  change q z-1-smoothBeurling h z=0 at he
  linear_combination -he

theorem smooth_beltrami_nondegenerate (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ F : ℂ → ℂ, ContDiff ℝ ∞ F ∧
      Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0) ∧
      (∀ z, partialBar F z=μ z*partialZ F z) ∧ (∀ z, partialZ F z ≠ 0) := by
  obtain ⟨h,q,hch,hq,hqne,hh,hB⟩ := smooth_nonvanishing_factor μ hcμ hk hk1 hb
  let F : ℂ → ℂ := fun z => z+cauchyTransform h z
  have hp (z : ℂ) : partialZ F z=q z ∧ partialBar F z=h z := by
    have hs := partials_add (f:=fun z : ℂ => z) (differentiableAt_id (𝕜:=ℝ))
      ((contDiff_cauchyTransform h).differentiable (by simp) z)
    refine ⟨?_,?_⟩
    · change partialZ (fun w => w+cauchyTransform h w) z=q z
      rw [hs.1,(partials_id z).1,(cauchyTransform_partials h z).2,hB]
    · change partialBar (fun w => w+cauchyTransform h w) z=h z
      rw [hs.2,(partials_id z).2,(cauchyTransform_partials h z).1,zero_add]
  refine ⟨F,contDiff_id.add (contDiff_cauchyTransform h),?_,?_,?_⟩
  · simpa [F] using cauchyTransform_zero_at_infty h
  · intro z; rw [(hp z).1,(hp z).2,hh]
  · intro z; rw [(hp z).1]; exact hqne z

lemma beltrami_fderiv_injective {F : ℂ → ℂ} {z μ : ℂ}
    (hμ : ‖μ‖ < 1) (he : partialBar F z=μ*partialZ F z)
    (hn : partialZ F z ≠ 0) : Function.Injective (fderiv ℝ F z) := by
  apply (fderiv ℝ F z).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change fderiv ℝ F z v=0 at hv
  rw [fderiv_wirtinger,he] at hv
  have hv' : v+μ*star v=0 := by
    apply (mul_eq_zero.mp (show partialZ F z*(v+μ*star v)=0 by linear_combination hv)).resolve_left hn
  have hnorm : ‖v‖ ≤ ‖μ‖*‖v‖ := by
    have heq : v= -(μ*star v) := eq_neg_iff_add_eq_zero.mpr hv'
    nth_rw 1 [heq]
    simp
  have hz : ‖v‖=0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hz

lemma localHomeomorph_of_beltrami {F : ℂ → ℂ} (hf : ContDiff ℝ ∞ F)
    (μ : ℂ → ℂ) (hb : ∀ z, ‖μ z‖ < 1)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (hn : ∀ z, partialZ F z ≠ 0) :
    IsLocalHomeomorphOn F univ := by
  intro z _
  have hi := beltrami_fderiv_injective (hb z) (he z) (hn z)
  let A : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ F z)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  have hd : HasFDerivAt F (A : ℂ →L[ℝ] ℂ) z :=
    (hf.differentiable (by simp) z).hasFDerivAt
  exact ⟨hf.contDiffAt.toOpenPartialHomeomorph F hd (by simp),
    hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),rfl⟩

lemma isProperMap_of_asymptotic_id {F : ℂ → ℂ} (hc : Continuous F)
    (ht : Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0)) : IsProperMap F := by
  apply isProperMap_iff_tendsto_cocompact.mpr
  refine ⟨hc,?_⟩
  apply (show Tendsto (fun z => ‖F z‖) (cocompact ℂ) atTop →
    Tendsto F (cocompact ℂ) (cocompact ℂ) from fun h => by
      simpa only [← cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp h)
  have he : ∀ᶠ z in cocompact ℂ, ‖F z-z‖ ≤ 1 :=
    (ht.norm.eventually (eventually_le_nhds (by norm_num : ‖(0:ℂ)‖ < 1)))
  have hn : Tendsto (fun z : ℂ => ‖z‖-1) (cocompact ℂ) atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right (cocompact ℂ) (-1)
      (tendsto_norm_cocompact_atTop (E:=ℂ))
  apply tendsto_atTop_mono' _ ?_ hn
  filter_upwards [he] with z hz
  have h := norm_sub_le (F z) (F z-z)
  have hh : F z-(F z-z)=z := by ring
  rw [hh] at h
  linarith

lemma global_homeomorph_of_proper_local {F : ℂ → ℂ} (hp : IsProperMap F)
    (hl : IsLocalHomeomorphOn F univ) : ∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ)=F := by
  have hcov : IsCoveringMap F := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    apply hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    · intro z _
      apply (hp.isCompact_preimage isCompact_singleton).finite
      apply IsDiscrete.of_openPartialHomeomorph F subset_rfl
      intro x hx
      obtain ⟨e,he,hFe⟩ := hl x (mem_univ _)
      exact ⟨e,he,hFe.symm⟩
    · simpa only [preimage_univ] using hl
  obtain ⟨g,⟨hg0,hg⟩,huniq⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id ℂ) (F 0) 0 rfl
  have hright : Function.RightInverse g F := fun x => congrFun hg x
  have hleft : Function.LeftInverse g F := by
    have he : F ∘ (g ∘ F)=F ∘ id := by ext x; exact hright (F x)
    have hh := hcov.eq_of_comp_eq (g.continuous.comp hp.continuous) continuous_id he 0 hg0
    exact fun x => congrFun hh x
  exact ⟨{ toFun := F
           invFun := g
           left_inv := hleft
           right_inv := hright
           continuous_toFun := hp.continuous
           continuous_invFun := g.continuous },rfl⟩

theorem smooth_beltrami_homeomorph (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ F : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (F : ℂ → ℂ) ∧
      Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0) ∧
      (∀ z, partialBar F z=μ z*partialZ F z) ∧ (∀ z, partialZ F z ≠ 0) := by
  obtain ⟨F,hF,ht,he,hn⟩ := smooth_beltrami_nondegenerate μ hcμ hk hk1 hb
  obtain ⟨e,heF⟩ := global_homeomorph_of_proper_local
    (isProperMap_of_asymptotic_id hF.continuous ht)
    (localHomeomorph_of_beltrami hF μ (fun z => (hb z).trans_lt hk1) he hn)
  refine ⟨e,?_⟩
  simpa only [heF] using And.intro hF (And.intro ht (And.intro he hn))

lemma contDiff_symm_beltrami (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ ∞ (F : ℂ → ℂ))
    (μ : ℂ → ℂ) (hb : ∀ z, ‖μ z‖ < 1)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (hn : ∀ z, partialZ F z ≠ 0) :
    ContDiff ℝ ∞ (F.symm : ℂ → ℂ) := by
  let A (z : ℂ) : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ F z)
    (LinearMap.ker_eq_bot.mpr (beltrami_fderiv_injective (hb z) (he z) (hn z)))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (beltrami_fderiv_injective (hb z) (he z) (hn z))))
  exact F.contDiff_symm (f₀':=A) (fun z => (hf.differentiable (by simp) z).hasFDerivAt) hf

lemma smooth_beltrami_l2_bound (μ h : SchwartzMap ℂ ℂ)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (he : ∀ z, h z-μ z*smoothBeurling h z=μ z) :
    ‖h.toLp 2 (μ:=volume)‖ ≤ ‖μ.toLp 2 (μ:=volume)‖/(1-k) := by
  obtain ⟨w,hw,hn,hunique⟩ := solve_beltrami_l2 μ μ.continuous.aestronglyMeasurable
    hk hk1 (.of_forall hb) (μ.toLp 2 (μ:=volume))
  have hh : h.toLp 2 (μ:=volume)-multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb)
      (beurling (h.toLp 2 (μ:=volume)))=μ.toLp 2 (μ:=volume) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (h.toLp 2 (μ:=volume))
      (multiplier μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling (h.toLp 2 (μ:=volume)))),
      multiplier_ae μ μ.continuous.aestronglyMeasurable hk (.of_forall hb) (beurling (h.toLp 2 (μ:=volume))),
      h.coeFn_toLp 2 volume,μ.coeFn_toLp 2 volume,(schwartz_smoothL2 h).beurling.representative_ae]
      with z h1 h2 h3 h4 h5
    simp only [Pi.sub_apply] at h1
    rw [h1,h2,h3,h4,h5]
    exact he z
  rw [hunique _ hh]
  exact hn

theorem smooth_principal_solution (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ (h : SchwartzMap ℂ ℂ) (F : ℂ ≃ₜ ℂ),
      HasCompactSupport (h : ℂ → ℂ) ∧
      (∀ z, F z=z+cauchyTransform h z) ∧
      ContDiff ℝ ∞ (F : ℂ → ℂ) ∧ ContDiff ℝ ∞ (F.symm : ℂ → ℂ) ∧
      (∀ z, partialBar F z=μ z*partialZ F z) ∧
      (∀ z, partialBar F z=h z ∧ partialZ F z=1+smoothBeurling h z) ∧
      ‖h.toLp 2 (μ:=volume)‖ ≤ ‖μ.toLp 2 (μ:=volume)‖/(1-k) := by
  obtain ⟨h,q,hch,hq,hqne,hh,hB⟩ := smooth_nonvanishing_factor μ hcμ hk hk1 hb
  let F : ℂ → ℂ := fun z => z+cauchyTransform h z
  have hF : ContDiff ℝ ∞ F := contDiff_id.add (contDiff_cauchyTransform h)
  have hp (z : ℂ) : partialBar F z=h z ∧ partialZ F z=1+smoothBeurling h z := by
    have hs := partials_add (f:=fun z : ℂ => z) (differentiableAt_id (𝕜:=ℝ))
      ((contDiff_cauchyTransform h).differentiable (by simp) z)
    refine ⟨?_,?_⟩
    · change partialBar (fun w => w+cauchyTransform h w) z=h z
      rw [hs.2,(partials_id z).2,(cauchyTransform_partials h z).1,zero_add]
    · change partialZ (fun w => w+cauchyTransform h w) z=1+smoothBeurling h z
      rw [hs.1,(partials_id z).1,(cauchyTransform_partials h z).2]
  have he (z : ℂ) : partialBar F z=μ z*partialZ F z := by rw [(hp z).1,(hp z).2,hB,hh]
  have hn (z : ℂ) : partialZ F z ≠ 0 := by rw [(hp z).2,hB]; exact hqne z
  have ht : Tendsto (fun z => F z-z) (cocompact ℂ) (𝓝 0) := by
    simpa [F] using cauchyTransform_zero_at_infty h
  obtain ⟨e,heF⟩ := global_homeomorph_of_proper_local
    (isProperMap_of_asymptotic_id hF.continuous ht)
    (localHomeomorph_of_beltrami hF μ (fun z => (hb z).trans_lt hk1) he hn)
  have heq (z : ℂ) : h z-μ z*smoothBeurling h z=μ z := by
    rw [hh]
    linear_combination -μ z*hB z
  refine ⟨h,e,hch,?_,?_,?_,?_,?_,smooth_beltrami_l2_bound μ h hk hk1 hb heq⟩
  · intro z; rw [heF]
  · simpa only [heF] using hF
  · apply contDiff_symm_beltrami e (by simpa only [heF] using hF) μ
      (fun z => (hb z).trans_lt hk1)
    · simpa only [heF] using he
    · simpa only [heF] using hn
  · simpa only [heF] using he
  · simpa only [heF] using hp

end CannonBeltrami

namespace CannonBeltrami
lemma partials_comp {F G : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F (G z)) (hg : DifferentiableAt ℝ G z) :
    partialZ (F ∘ G) z=partialZ F (G z)*partialZ G z+partialBar F (G z)*star (partialBar G z) ∧
    partialBar (F ∘ G) z=partialZ F (G z)*partialBar G z+partialBar F (G z)*star (partialZ G z) := by
  have hd := (hf.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  constructor
  · change (fderiv ℝ (F ∘ G) z 1-Complex.I*fderiv ℝ (F ∘ G) z Complex.I)/2= _
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_wirtinger F (G z),fderiv_wirtinger F (G z)]
    simp only [partialZ,partialBar,map_div₀,map_add,map_mul,Complex.star_def,
      Complex.conj_I,map_ofNat]
    ring_nf
  · change (fderiv ℝ (F ∘ G) z 1+Complex.I*fderiv ℝ (F ∘ G) z Complex.I)/2= _
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_wirtinger F (G z),fderiv_wirtinger F (G z)]
    simp only [partialZ,partialBar,map_div₀,map_sub,map_mul,Complex.star_def,
      Complex.conj_I,map_ofNat]
    ring_nf

lemma inverse_partialBar (F : ℂ ≃ₜ ℂ) (hf : Differentiable ℝ (F : ℂ → ℂ))
    (hg : Differentiable ℝ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    (he : ∀ z, partialBar F z=μ z*partialZ F z)
    (hn : ∀ z, partialZ F z ≠ 0) (z : ℂ) :
    partialBar F.symm z= -μ (F.symm z)*star (partialZ F.symm z) := by
  have hp := (partials_comp (hf (F.symm z)) (hg z)).2
  have hid : (F : ℂ → ℂ) ∘ F.symm=id := funext F.apply_symm_apply
  rw [hid] at hp
  change partialBar (fun w : ℂ => w) z = _ at hp
  rw [(partials_id z).2,he] at hp
  apply mul_left_cancel₀ (hn (F.symm z))
  linear_combination -hp

end CannonBeltrami

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonBeltrami

lemma realCLM_det_wirtinger (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) :
    D.det = ‖a‖^2-‖b‖^2 := by
  change LinearMap.det (D : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe,
    Complex.coe_basisOneI,Matrix.cons_val_zero,Matrix.cons_val_one,
    Complex.coe_basisOneI_repr,hD,
    star_one,mul_one,Complex.star_def,Complex.conj_I]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im]
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  ring

lemma realCLM_opNorm_wirtinger (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) : ‖D‖ ≤ ‖a‖+‖b‖ := by
  apply D.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  rw [hD]
  calc
    _ ≤ ‖a*v‖+‖b*star v‖ := norm_add_le _ _
    _ = (‖a‖+‖b‖)*‖v‖ := by simp only [norm_mul,norm_star]; ring

theorem wirtinger_energy_distortion (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hba : ‖b‖ ≤ k*‖a‖) :
    0 ≤ D.det ∧ ‖D‖^2 ≤ ((1+k)/(1-k))*|D.det| := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hnorm_sq : ‖b‖^2 ≤ k^2*‖a‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hb (mul_nonneg hk ha)).mpr hba
  have hk_sq : k^2 ≤ 1 := by nlinarith
  have hd := realCLM_det_wirtinger D a b hD
  have hdet : 0 ≤ D.det := by
    rw [hd]
    exact sub_nonneg.mpr (hnorm_sq.trans
      ((mul_le_mul_of_nonneg_right hk_sq (sq_nonneg ‖a‖)).trans_eq (one_mul _)))
  refine ⟨hdet,?_⟩
  rw [abs_of_nonneg hdet,hd]
  have hn := realCLM_opNorm_wirtinger D a b hD
  have hns : ‖D‖^2 ≤ (‖a‖+‖b‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg ha hb)).mpr hn
  have hprod : 0 ≤ (k*‖a‖-‖b‖)*(‖a‖+‖b‖) :=
    mul_nonneg (sub_nonneg.mpr hba) (add_nonneg ha hb)
  apply hns.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
  nlinarith

end CannonBeltrami

namespace CannonBeltrami

def twoPointNormalize (F : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ where
  toFun z := (F z-F 0)/(F 1-F 0)
  invFun w := F.symm ((F 1-F 0)*w+F 0)
  left_inv z := by
    have hc : F 1-F 0 ≠ 0 := sub_ne_zero.mpr (fun h => one_ne_zero (F.injective h))
    simp [mul_div_cancel₀ _ hc]
  right_inv w := by
    have hc : F 1-F 0 ≠ 0 := sub_ne_zero.mpr (fun h => one_ne_zero (F.injective h))
    simp [hc]
  continuous_toFun := (F.continuous.sub continuous_const).div_const _
  continuous_invFun := F.symm.continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

@[simp] lemma twoPointNormalize_apply (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    twoPointNormalize F z=(F z-F 0)/(F 1-F 0) := rfl
@[simp] lemma twoPointNormalize_symm_apply (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    (twoPointNormalize F).symm z=F.symm ((F 1-F 0)*z+F 0) := rfl

lemma twoPointNormalize_zero (F : ℂ ≃ₜ ℂ) : twoPointNormalize F 0=0 := by simp
lemma twoPointNormalize_one (F : ℂ ≃ₜ ℂ) : twoPointNormalize F 1=1 := by
  rw [twoPointNormalize_apply,div_self]
  exact sub_ne_zero.mpr (fun h => one_ne_zero (F.injective h))

lemma twoPointNormalize_contDiff (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ ∞ (F : ℂ → ℂ)) (hF' : ContDiff ℝ ∞ (F.symm : ℂ → ℂ)) :
    ContDiff ℝ ∞ (twoPointNormalize F : ℂ → ℂ) ∧
      ContDiff ℝ ∞ ((twoPointNormalize F).symm : ℂ → ℂ) := by
  exact ⟨(hF.sub contDiff_const).div_const _,
    hF'.comp ((contDiff_const.mul contDiff_id).add contDiff_const)⟩

lemma twoPointNormalize_partials (F : ℂ ≃ₜ ℂ) (hF : Differentiable ℝ (F : ℂ → ℂ)) (z : ℂ) :
    partialZ (twoPointNormalize F) z=partialZ F z/(F 1-F 0) ∧
      partialBar (twoPointNormalize F) z=partialBar F z/(F 1-F 0) := by
  have hd : fderiv ℝ (twoPointNormalize F : ℂ → ℂ) z=
      (F 1-F 0)⁻¹ • fderiv ℝ (F : ℂ → ℂ) z := by
    change fderiv ℝ (fun w => (F w-F 0)/(F 1-F 0)) z = _
    have he : (fun w => (F w-F 0)/(F 1-F 0))=(fun w => (F 1-F 0)⁻¹*(F w-F 0)) := by
      funext w; ring
    rw [he]
    simpa using (((hF z).hasFDerivAt.sub_const (F 0)).const_mul (F 1-F 0)⁻¹).fderiv
  unfold partialZ partialBar
  rw [hd]
  simp only [smul_apply,smul_eq_mul]
  constructor <;> ring

theorem normalized_smooth_beltrami_solution (μ : SchwartzMap ℂ ℂ)
    (hcμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ F : ℂ ≃ₜ ℂ, F 0=0 ∧ F 1=1 ∧
      ContDiff ℝ ∞ (F : ℂ → ℂ) ∧ ContDiff ℝ ∞ (F.symm : ℂ → ℂ) ∧
      (∀ z, partialBar F z=μ z*partialZ F z) ∧
      (∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ ((1+k)/(1-k))*|(fderiv ℝ (F : ℂ → ℂ) z).det|) ∧
      (∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤ ((1+k)/(1-k))*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det|) := by
  obtain ⟨G,hG,ht,he,hn⟩ := smooth_beltrami_homeomorph μ hcμ hk hk1 hb
  have hG' := contDiff_symm_beltrami G hG μ (fun z => (hb z).trans_lt hk1) he hn
  let F := twoPointNormalize G
  have hs := twoPointNormalize_contDiff G hG hG'
  have hp (z : ℂ) := twoPointNormalize_partials G (hG.differentiable (by simp)) z
  have heF (z : ℂ) : partialBar F z=μ z*partialZ F z := by
    change partialBar (twoPointNormalize G) z=_
    rw [(hp z).2,he,(hp z).1]
    ring
  have hnF (z : ℂ) : partialZ F z ≠ 0 := by
    rw [(hp z).1]
    exact div_ne_zero (hn z) (sub_ne_zero.mpr (fun h => one_ne_zero (G.injective h)))
  refine ⟨F,twoPointNormalize_zero G,twoPointNormalize_one G,hs.1,hs.2,heF,?_,?_⟩
  · intro z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F z) hk hk1 (by
      rw [heF,norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))).2
  · intro z
    have hi := inverse_partialBar F (hs.1.differentiable (by simp))
      (hs.2.differentiable (by simp)) μ heF hnF z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F.symm z) hk hk1 (by
      rw [hi,norm_mul,norm_neg,norm_star]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))).2

end CannonBeltrami

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
