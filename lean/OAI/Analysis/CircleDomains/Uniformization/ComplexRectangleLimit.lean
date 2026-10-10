import Mathlib.Analysis.Complex.HasPrimitives
import OAI.Geometry.Cannon.Beltrami.CauchySymbol

namespace OAI

/-! Rectangular Morera passage for smooth maps with vanishing antiholomorphic
error. Uniform convergence is needed only on the four compact edges. -/
open Set Function Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

def complexRectangleFlux (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫x : ℝ in z.re..w.re,f (x+z.im*I))-(∫x : ℝ in z.re..w.re,f (x+w.im*I))+
    I*(∫y : ℝ in z.im..w.im,f (w.re+y*I))-I*(∫y : ℝ in z.im..w.im,f (z.re+y*I))

lemma locally_uniform_curve_integral {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀n,Continuous (f n)) (hl : TendstoLocallyUniformly f g atTop)
    (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ) :
    Tendsto (fun n => ∫t in a..b,f n (γ t)) atTop (𝓝 (∫t in a..b,g (γ t))) := by
  have ht := tendstoLocallyUniformly_iff_forall_isCompact.mp hl
    (γ '' uIcc a b) (isCompact_uIcc.image hγ)
  have hc : TendstoUniformlyOn (fun n t => f n (γ t)) (fun t => g (γ t)) atTop (uIcc a b) :=
    (ht.comp γ).mono (fun t ht => mem_image_of_mem γ ht)
  exact hc.tendsto_intervalIntegral_of_continuousOn (.of_forall fun n => (hf n |>.comp hγ).continuousOn)

lemma complexRectangleFlux_tendsto {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀n,Continuous (f n)) (hl : TendstoLocallyUniformly f g atTop) (z w : ℂ) :
    Tendsto (fun n => complexRectangleFlux (f n) z w) atTop (𝓝 (complexRectangleFlux g z w)) := by
  have h₁ := locally_uniform_curve_integral hf hl (fun x => x+z.im*I) (by fun_prop) z.re w.re
  have h₂ := locally_uniform_curve_integral hf hl (fun x => x+w.im*I) (by fun_prop) z.re w.re
  have h₃ := locally_uniform_curve_integral hf hl (fun y => w.re+y*I) (by fun_prop) z.im w.im
  have h₄ := locally_uniform_curve_integral hf hl (fun y => z.re+y*I) (by fun_prop) z.im w.im
  exact ((h₁.sub h₂).add (h₃.const_mul I)).sub (h₄.const_mul I)

lemma complexRectangleFlux_eq_bar_integral {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (z w : ℂ) :
    complexRectangleFlux f z w=(2*I)*(∫x : ℝ in z.re..w.re,
      ∫y : ℝ in z.im..w.im,partialBar f (x+y*I)) := by
  have hi : IntegrableOn (fun p => I • fderiv ℝ f p 1-fderiv ℝ f p I)
      (uIcc z.re w.re ×ℂ uIcc z.im w.im) :=
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).const_smul I |>.sub
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)).continuousOn.integrableOn_compact
        (isCompact_uIcc.reProdIm isCompact_uIcc)
  have he := integral_boundary_rect_of_differentiableOn_real f z w
    (hf.differentiable (by norm_num)).differentiableOn hi
  have hid (p : ℂ) : I • fderiv ℝ f p 1-fderiv ℝ f p I=(2*I)*partialBar f p := by
    simp only [smul_eq_mul,partialBar]
    ring_nf
    simp [I_sq]
    ring
  change complexRectangleFlux f z w=_ at he
  rw [he]
  simp_rw [hid,intervalIntegral.integral_const_mul]

lemma differentiableOn_of_vanishing_rectangle_errors {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀n,ContDiff ℝ 1 (f n))
    (hl : TendstoLocallyUniformly f g atTop)
    (he : ∀z w,Rectangle z w⊆U →
      Tendsto (fun n => ∫x : ℝ in z.re..w.re,
        ∫y : ℝ in z.im..w.im,partialBar (f n) (x+y*I)) atTop (𝓝 0)) :
    DifferentiableOn ℂ g U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,(hl.continuous (.of_forall fun n => (hf n).continuous)).continuousOn⟩
  intro z w hzw
  have hz : complexRectangleFlux g z w=0 := by
    apply tendsto_nhds_unique (complexRectangleFlux_tendsto (fun n => (hf n).continuous) hl z w)
    have ht := (he z w hzw).const_mul (2*I)
    simpa only [complexRectangleFlux_eq_bar_integral (hf _),mul_zero] using ht
  rw [←add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq]
  exact hz

end CircleDomainRigidity

end

end OAI
