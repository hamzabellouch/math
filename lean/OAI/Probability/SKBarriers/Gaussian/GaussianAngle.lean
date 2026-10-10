import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianCovariance

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def gaussianAngle (f g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ p, f p.1*g (gaussianMix (Real.cos θ) (Real.sin θ) p) ∂gaussianPair

theorem gaussianAngle_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    Continuous (gaussianAngle f g) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  apply continuousAt_of_dominated (bound:=fun _ : ℝ × ℝ => B*C)
  · exact Eventually.of_forall (fun a => ((hf.comp continuous_fst).mul
      (hg.comp (by unfold gaussianMix; fun_prop))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hb _) (hc _) (abs_nonneg _) hB))
  · exact integrable_const _
  · exact ae_of_all _ (fun p => (continuous_const.mul
      (hg.comp (by unfold gaussianMix; fun_prop))).continuousAt)

theorem gaussian_integrable_bounded {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f (gaussianReal 0 1) := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem gaussian_integrable_sq_bounded {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Integrable (fun x => f x^2) (gaussianReal 0 1) :=
  gaussian_integrable_bounded (hf.pow 2) (fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x))

theorem gaussianAngle_zero (f : ℝ → ℝ) (hf : Continuous f) :
    gaussianAngle f f 0=∫ x, f x^2 ∂gaussianReal 0 1 := by
  have H := gaussianPair_fst.integral_comp (hf.pow 2).aestronglyMeasurable
  simpa only [gaussianAngle,gaussianMix,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,
    add_zero,pow_two,Function.comp_def,Pi.mul_apply] using H

theorem gaussianAngle_pi_half {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    gaussianAngle f g (Real.pi/2)=(∫ x, f x ∂gaussianReal 0 1)*(∫ x, g x ∂gaussianReal 0 1) := by
  have hi : Integrable (fun p : ℝ × ℝ => f p.1*g p.2) gaussianPair :=
    gaussianPair_integrable_bounded (by fun_prop) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hb _) (hc _) (abs_nonneg _) hB)
  simp only [gaussianAngle,gaussianMix,Real.cos_pi_div_two,Real.sin_pi_div_two,
    zero_mul,one_mul,zero_add,gaussianPair]
  rw [integral_prod _ hi]
  simp only [integral_const_mul,integral_mul_const]

theorem gaussianAngle_le_square {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (θ : ℝ) :
    gaussianAngle f f θ ≤ ∫ x, f x^2 ∂gaussianReal 0 1 := by
  have hfc : Continuous (fun p : ℝ × ℝ => f p.1) := hf.comp continuous_fst
  have hgc : Continuous (fun p : ℝ × ℝ => f (gaussianMix (Real.cos θ) (Real.sin θ) p)) :=
    hf.comp (by unfold gaussianMix; fun_prop)
  have hi : Integrable (fun p : ℝ × ℝ => f p.1*f (gaussianMix (Real.cos θ) (Real.sin θ) p)) gaussianPair :=
    gaussianPair_integrable_bounded (hfc.mul hgc) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hB)
  have hb2 (x : ℝ) : |f x^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)
  have hf2 := gaussianPair_integrable_bounded (hfc.pow 2) (fun p => hb2 p.1)
  have hg2 := gaussianPair_integrable_bounded (hgc.pow 2) (fun p => hb2 _)
  have H := integral_mono (hi.const_mul 2) (hf2.add hg2)
    (fun p => by dsimp; nlinarith [sq_nonneg (f p.1-f (gaussianMix (Real.cos θ) (Real.sin θ) p))])
  simp only [Pi.add_apply,Pi.pow_apply] at hf2 hg2 H
  have Hplus := integral_add hf2 hg2
  simp only [Pi.pow_apply] at Hplus
  rw [integral_const_mul,Hplus] at H
  have HA := gaussianPair_fst.integral_comp (hf.pow 2).aestronglyMeasurable
  have HB := (gaussianMix_law (Real.cos θ) (Real.sin θ)
    (by nlinarith [Real.sin_sq_add_cos_sq θ])).integral_comp (hf.pow 2).aestronglyMeasurable
  simp only [Function.comp_def,Pi.pow_apply] at HA HB
  rw [HA,HB] at H
  exact (by change _ ≤ _; unfold gaussianAngle; linarith)

theorem gaussian_variance_pos {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B)
    (hne : ¬∃ c, ∀ x, f x=c) :
    (∫ x, f x ∂gaussianReal 0 1)^2 < ∫ x, f x^2 ∂gaussianReal 0 1 := by
  let a : ℝ := ∫ x, f x ∂gaussianReal 0 1
  have hint := gaussian_integrable_bounded hf hb
  have hi2 := gaussian_integrable_sq_bounded hf hB hb
  have his : Integrable (fun x => (f x-a)^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hf.sub continuous_const) (B:=B+|a|) (by positivity)
      (fun x => (abs_sub _ _).trans (add_le_add (hb x) (le_refl _)))
  have hp : 0<∫ x, (f x-a)^2 ∂gaussianReal 0 1 := by
    apply lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (f x-a)))
    intro he
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x-a)) his).mp he.symm
    have hv := hz.filter_mono (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0)≠0)).ae_le
    have heq := MeasureTheory.Measure.eq_of_ae_eq hv ((hf.sub continuous_const).pow 2) continuous_const
    apply hne
    refine ⟨a,fun x => ?_⟩
    have H := congrFun heq x
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp H)
  have he : (∫ x, (f x-a)^2 ∂gaussianReal 0 1)=
      (∫ x, f x^2 ∂gaussianReal 0 1)-a^2 := by
    simp_rw [show ∀ x, (f x-a)^2=f x^2-2*a*f x+a^2 by intro x; ring]
    have Hplus := integral_add (hi2.sub (hint.const_mul (2*a))) (integrable_const (a^2))
    have Hsub := integral_sub hi2 (hint.const_mul (2*a))
    simp only [Pi.sub_apply] at Hplus Hsub
    rw [Hplus,Hsub,integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
    dsimp only [a]; ring
  rw [he] at hp
  exact sub_pos.mp hp

end SK.Analytic

end
end

end OAI
