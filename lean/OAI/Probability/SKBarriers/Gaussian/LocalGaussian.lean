import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic
import OAI.Probability.SKBarriers.Gaussian.GaussianDomination

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def GaussianLocallyDominated {E F : Type} [Norm E] [Norm F]
    (f : E × ℝ → F) : Prop :=
  ∀ R : ℝ, ∃ b : ℝ → ℝ, Integrable b (gaussianReal 0 1) ∧
    ∀ x y, ‖x‖ ≤ R → ‖f (x,y)‖ ≤ b y

theorem GaussianLocallyDominated.of_norm_le {E F G : Type} [Norm E] [Norm F] [Norm G]
    {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) {g : E × ℝ → G} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ z, ‖g z‖ ≤ K*‖f z‖) : GaussianLocallyDominated g := by
  intro R
  obtain ⟨b,hb,hh⟩ := hg R
  exact ⟨fun y => K*b y,hb.const_mul _,fun x y hx =>
    (h (x,y)).trans (mul_le_mul_of_nonneg_left (hh x y hx) hK)⟩

section LocalGaussian
variable {E F G : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G]

theorem HasExpGrowth.locallyDominated {f : E × ℝ → F} (hf : HasExpGrowth f) :
    GaussianLocallyDominated f := hf.gaussian_section_bound

theorem GaussianLocallyDominated.integrable_section {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) (hf : Continuous f) (x : E) :
    Integrable (fun y => f (x,y)) (gaussianReal 0 1) := by
  obtain ⟨b,hb,hbound⟩ := hg ‖x‖
  exact hb.mono' (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (fun y => hbound x y le_rfl))

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem GaussianLocallyDominated.clm {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) (L : F →L[ℝ] G) :
    GaussianLocallyDominated (fun z => L (f z)) :=
  hg.of_norm_le (norm_nonneg L) (fun z => L.le_opNorm (f z))

theorem GaussianLocallyDominated.continuous_integral {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) (hf : Continuous f) :
    Continuous (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨b,hb,hbound⟩ := hg (‖x₀‖+1)
  apply continuousAt_of_dominated (bound := b)
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
    exact ae_of_all _ (fun y => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt)

variable [NormedSpace ℝ E]

theorem hasFDerivAt_local_gaussian_integral (f : E × ℝ → F)
    (f₁ : E × ℝ → E →L[ℝ] F) (hf : Continuous f) (hf₁ : Continuous f₁)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated f₁)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x) (x₀ : E) :
    HasFDerivAt (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)
      (∫ y, f₁ (x₀,y) ∂gaussianReal 0 1) x₀ := by
  obtain ⟨b,hb,hbound⟩ := hg₁ (‖x₀‖+1)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
    (Metric.ball_mem_nhds x₀ (by norm_num))
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact hg.integrable_section hf x₀
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun y x hx => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y x _ => hd x y)

theorem contDiff_two_local_gaussian_integral (f : E × ℝ → F)
    (f₁ : E × ℝ → E →L[ℝ] F) (f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated f₁)
    (hg₂ : GaussianLocallyDominated f₂)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x)
    (hd₁ : ∀ x y, HasFDerivAt (fun z => f₁ (z,y)) (f₂ (x,y)) x) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  have hc₁ : ContDiff ℝ 1 (fun x => ∫ y, f₁ (x,y) ∂gaussianReal 0 1) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun x => ∫ y, f₂ (x,y) ∂gaussianReal 0 1, ?_, ?_⟩
    · exact contDiff_zero.mpr (hg₂.continuous_integral hf₂)
    · exact hasFDerivAt_local_gaussian_integral f₁ f₂ hf₁ hf₂ hg₁ hg₂ hd₁
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  exact ⟨_,hc₁,hasFDerivAt_local_gaussian_integral f f₁ hf hf₁ hg hg₁ hd⟩

theorem contDiff_two_local_gaussian_integral_fderiv (f : E × ℝ → F)
    (hf : ContDiff ℝ 2 f) (hg : GaussianLocallyDominated f)
    (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (hg₂ : GaussianLocallyDominated (fderiv ℝ (fderiv ℝ f))) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  let L := ContinuousLinearMap.inl ℝ E ℝ
  let T := (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip L
  let T₁ := (ContinuousLinearMap.compL ℝ E (E × ℝ) (E →L[ℝ] F)).flip L
  let S := (ContinuousLinearMap.compL ℝ (E × ℝ) ((E × ℝ) →L[ℝ] F) (E →L[ℝ] F)) T
  let f₁ : E × ℝ → E →L[ℝ] F := fun z => T (fderiv ℝ f z)
  let f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F := fun z => T₁ (S (fderiv ℝ (fderiv ℝ f) z))
  have hf₁ : ContDiff ℝ 1 f₁ := T.contDiff.comp (hf.fderiv_right (by norm_num))
  have hf₂ : Continuous f₂ := T₁.continuous.comp (S.continuous.comp
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).fderiv_right (m := 0) (by norm_num)).continuous)
  have hg₂T : GaussianLocallyDominated f₂ := by
    apply hg₂.of_norm_le (K := ‖T₁‖*‖S‖) (mul_nonneg (norm_nonneg T₁) (norm_nonneg S))
    intro z
    calc
      ‖f₂ z‖ ≤ ‖T₁‖*‖S (fderiv ℝ (fderiv ℝ f) z)‖ := T₁.le_opNorm _
      _ ≤ ‖T₁‖*(‖S‖*‖fderiv ℝ (fderiv ℝ f) z‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  apply contDiff_two_local_gaussian_integral f f₁ f₂ hf.continuous hf₁.continuous hf₂ hg
    (hg₁.clm T) hg₂T
  · intro x y
    exact (hf.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  · intro x y
    have hd := T.hasFDerivAt.comp (x,y)
      ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) (x,y)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,y)) L x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
    convert! hd.comp x hxy using 1
end LocalGaussian
end SK.Analytic

end
end

end

end OAI
