import OAI.Analysis.CircleDomains.Uniformization.ComplexRectangleLimit

namespace OAI

/-! A local rectangular Morera passage, allowing the smooth approximants'
poles outside the fixed open set and allowing a finite initial segment. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma locally_uniform_curve_integral_on {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ᶠn in atTop,ContinuousOn (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (a b : ℝ) (hsub : MapsTo γ (uIcc a b) U) :
    Tendsto (fun n => ∫t in a..b,f n (γ t)) atTop (𝓝 (∫t in a..b,g (γ t))) := by
  have ht := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl
    (γ '' uIcc a b) (image_subset_iff.mpr hsub) (isCompact_uIcc.image hγ)
  have hc : TendstoUniformlyOn (fun n t => f n (γ t)) (fun t => g (γ t)) atTop (uIcc a b) :=
    (ht.comp γ).mono (fun t ht => mem_image_of_mem γ ht)
  exact hc.tendsto_intervalIntegral_of_continuousOn
    (hf.mono fun n hn => hn.comp hγ.continuousOn hsub)

lemma complexRectangleFlux_tendsto_on {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ᶠn in atTop,ContinuousOn (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U) (z w : ℂ) (hzw : Rectangle z w⊆U) :
    Tendsto (fun n => complexRectangleFlux (f n) z w) atTop (𝓝 (complexRectangleFlux g z w)) := by
  have h₁ := locally_uniform_curve_integral_on hU hf hl (fun x => x+z.im*I)
    (by fun_prop) z.re w.re (fun x hx => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro hx (left_mem_uIcc : z.im∈uIcc z.im w.im)))
  have h₂ := locally_uniform_curve_integral_on hU hf hl (fun x => x+w.im*I)
    (by fun_prop) z.re w.re (fun x hx => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro hx (right_mem_uIcc : w.im∈uIcc z.im w.im)))
  have h₃ := locally_uniform_curve_integral_on hU hf hl (fun y => w.re+y*I)
    (by fun_prop) z.im w.im (fun y hy => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro (right_mem_uIcc : w.re∈uIcc z.re w.re) hy))
  have h₄ := locally_uniform_curve_integral_on hU hf hl (fun y => z.re+y*I)
    (by fun_prop) z.im w.im (fun y hy => hzw (by change _ ∈ _ ∧ _ ∈ _; simpa using And.intro (left_mem_uIcc : z.re∈uIcc z.re w.re) hy))
  exact ((h₁.sub h₂).add (h₃.const_mul I)).sub (h₄.const_mul I)

lemma complexRectangleFlux_eq_bar_integral_on {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f U) (z w : ℂ) (hzw : Rectangle z w⊆U) :
    complexRectangleFlux f z w=(2*I)*(∫x : ℝ in z.re..w.re,
      ∫y : ℝ in z.im..w.im,partialBar f (x+y*I)) := by
  have hd := hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hi : IntegrableOn (fun p => I • fderiv ℝ f p 1-fderiv ℝ f p I) (Rectangle z w) :=
    ((hd.clm_apply continuousOn_const).const_smul I |>.sub
      (hd.clm_apply continuousOn_const)).mono hzw |>.integrableOn_compact
        (isCompact_uIcc.reProdIm isCompact_uIcc)
  have he := integral_boundary_rect_of_differentiableOn_real f z w
    ((hf.differentiableOn (by norm_num)).mono hzw) hi
  have hid (p : ℂ) : I • fderiv ℝ f p 1-fderiv ℝ f p I=(2*I)*partialBar f p := by
    simp only [smul_eq_mul,partialBar]
    ring_nf
    simp [I_sq]
    ring
  change complexRectangleFlux f z w=_ at he
  rw [he]
  simp_rw [hid,intervalIntegral.integral_const_mul]

lemma differentiableOn_of_local_rectangle_errors {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠn in atTop,ContDiffOn ℝ 1 (f n) U)
    (hl : TendstoLocallyUniformlyOn f g atTop U)
    (he : ∀z w,Rectangle z w⊆U →
      Tendsto (fun n => ∫x : ℝ in z.re..w.re,
        ∫y : ℝ in z.im..w.im,partialBar (f n) (x+y*I)) atTop (𝓝 0)) :
    DifferentiableOn ℂ g U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,hl.continuousOn (hf.frequently.mono fun n hn => hn.continuousOn)⟩
  intro z w hzw
  have hz : complexRectangleFlux g z w=0 := by
    apply tendsto_nhds_unique (complexRectangleFlux_tendsto_on hU
      (hf.mono fun n hn => hn.continuousOn) hl z w hzw)
    have ht := (he z w hzw).const_mul (2*I)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hf] with n hn
    exact (complexRectangleFlux_eq_bar_integral_on hU hn z w hzw).symm
  rw [←add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq]
  exact hz

end CircleDomainRigidity

end

end OAI
