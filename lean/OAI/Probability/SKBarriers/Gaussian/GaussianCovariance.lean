import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianGrowth
import OAI.Probability.SKBarriers.Gaussian.GaussianIntegration
import OAI.Probability.SKBarriers.Gaussian.GaussianRotation

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianPair_integrable_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) : Integrable f gaussianPair := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hB p)

theorem gaussianPair_integrable_linear_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hB : ∀ p, |f p| ≤ B*(|p.1|+|p.2|)+C) : Integrable f gaussianPair := by
  have hi := ((gaussianPair_fst.hasGaussianLaw.integrable.norm.add
    gaussianPair_snd.hasGaussianLaw.integrable.norm).const_mul B).add (integrable_const C)
  apply hi.mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hB p)

theorem gaussianPair_rotation_derivative {f g dg : ℝ → ℝ}
    (hf : Continuous f) (hd : ∀ x, HasDerivAt g (dg x) x) (hc : Continuous dg)
    {B D C : ℝ} (hB : 0 ≤ B) (_hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdg : ∀ x, |g x| ≤ D) (hdc : ∀ x, |dg x| ≤ C) (θ : ℝ) :
    HasDerivAt (fun a => ∫ p, f p.1*g (gaussianMix (Real.cos a) (Real.sin a) p) ∂gaussianPair)
      (∫ p, f p.1*dg (gaussianMix (Real.cos θ) (Real.sin θ) p)*
        gaussianMix (-Real.sin θ) (Real.cos θ) p ∂gaussianPair) θ := by
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm (a : ℝ) (p : ℝ × ℝ) :
      |gaussianMix (-Real.sin a) (Real.cos a) p| ≤ |p.1|+|p.2| := by
    unfold gaussianMix
    calc
      _ ≤ |-Real.sin a*p.1|+|Real.cos a*p.2| := abs_add_le _ _
      _ ≤ |p.1|+|p.2| := by
        simp only [abs_mul,abs_neg]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
  have hi : Integrable (fun p : ℝ × ℝ => B*C*(|p.1|+|p.2|)) gaussianPair := by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using
      ((gaussianPair_fst.hasGaussianLaw.integrable.norm.add
        gaussianPair_snd.hasGaussianLaw.integrable.norm).const_mul (B*C))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (x₀:=θ)
    (F:=fun a p => f p.1*g (gaussianMix (Real.cos a) (Real.sin a) p))
    (F':=fun a p => f p.1*dg (gaussianMix (Real.cos a) (Real.sin a) p)*gaussianMix (-Real.sin a) (Real.cos a) p)
    (bound:=fun p : ℝ × ℝ => B*C*(|p.1|+|p.2|)) (by simp) _ _ _ _ hi _).2
  · exact Eventually.of_forall (fun a => (hf.comp continuous_fst |>.mul
      (hg.comp (by unfold gaussianMix; fun_prop))).aestronglyMeasurable)
  · apply gaussianPair_integrable_bounded (hf.comp continuous_fst |>.mul
      (hg.comp (by unfold gaussianMix; fun_prop)))
    intro p; simp only [Function.comp_def,Pi.mul_apply,abs_mul]; exact mul_le_mul (hb _) (hdg _) (abs_nonneg _) hB
  · exact (((hf.comp continuous_fst).mul (hc.comp (by unfold gaussianMix; fun_prop))).mul
      (by unfold gaussianMix; fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun p a _ => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hb _) (hdc _) (abs_nonneg _) hB) (hm a p)
        (abs_nonneg _) (mul_nonneg hB hC))
  · exact ae_of_all _ (fun p a _ => by
      have H := (hd (gaussianMix (Real.cos a) (Real.sin a) p)).comp a
        (((Real.hasDerivAt_cos a).mul_const p.1).add ((Real.hasDerivAt_sin a).mul_const p.2))
      simpa only [gaussianMix,mul_assoc,Function.comp_def,Pi.add_apply] using H.const_mul (f p.1))

theorem gaussianPair_rotation_stein {f df k : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df) (hk : Continuous k)
    {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) (hkd : ∀ x, |k x| ≤ D) (θ : ℝ) :
    (∫ p, f p.1*k (gaussianMix (Real.cos θ) (Real.sin θ) p)*
        gaussianMix (-Real.sin θ) (Real.cos θ) p ∂gaussianPair)=
      -Real.sin θ*(∫ p, df p.1*k (gaussianMix (Real.cos θ) (Real.sin θ) p) ∂gaussianPair) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let A : ℝ × ℝ → ℝ := fun p => f (gaussianMix (Real.cos θ) (-Real.sin θ) p)*k p.1*p.2
  let A' : ℝ × ℝ → ℝ := fun p => df (gaussianMix (Real.cos θ) (-Real.sin θ) p)*k p.1
  have hAc : Continuous A := by dsimp [A,gaussianMix]; fun_prop
  have hA'c : Continuous A' := by dsimp [A',gaussianMix]; fun_prop
  have heq (p : ℝ × ℝ) : gaussianMix (Real.cos θ) (-Real.sin θ) (gaussianRotate θ p)=p.1 := by
    have H := congrArg Prod.fst (gaussianRotate_inverse θ p)
    simpa only [gaussianRotate,Real.cos_neg,Real.sin_neg] using H
  have hA : (fun p => A (gaussianRotate θ p))=(fun p => f p.1*
      k (gaussianMix (Real.cos θ) (Real.sin θ) p)*gaussianMix (-Real.sin θ) (Real.cos θ) p) := by
    funext p; dsimp only [A]; rw [heq]; rfl
  have hA' : (fun p => A' (gaussianRotate θ p))=(fun p => df p.1*
      k (gaussianMix (Real.cos θ) (Real.sin θ) p)) := by
    funext p; dsimp only [A']; rw [heq]; rfl
  have HA := (gaussianRotate_law θ).integral_comp hAc.aestronglyMeasurable
  have HA' := (gaussianRotate_law θ).integral_comp hA'c.aestronglyMeasurable
  simp only [Function.comp_def] at HA HA'
  rw [← hA,← hA',HA,HA']
  have hAi : Integrable A gaussianPair := by
    apply gaussianPair_integrable_linear_bounded hAc (B:=B*D) (C:=0)
    intro p
    dsimp [A]; rw [abs_mul,abs_mul]
    calc
      _ ≤ B*D*|p.2| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hb _) (hkd _) (abs_nonneg _) hB) (abs_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hB hD,abs_nonneg p.1]
  have hA'i : Integrable A' gaussianPair := by
    apply gaussianPair_integrable_bounded hA'c
    intro p
    dsimp [A']; rw [abs_mul]
    exact mul_le_mul (hdf _) (hkd _) (abs_nonneg _) hC
  rw [show gaussianPair=(gaussianReal 0 1).prod (gaussianReal 0 1) from rfl,
    integral_prod _ hAi,integral_prod _ hA'i,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    have hfc : Continuous (fun z : ℝ => f (Real.cos θ*y-Real.sin θ*z)) := by fun_prop
    have hdfc : Continuous (fun z : ℝ => -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z)) := by fun_prop
    have hfint : Integrable (fun z : ℝ => f (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) :=
      (integrable_const B).mono' hfc.aestronglyMeasurable (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb _))
    have hdint : Integrable (fun z : ℝ => -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) := by
      apply (integrable_const (|Real.sin θ| *C)).mono' hdfc.aestronglyMeasurable
      exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_mul,abs_neg]; exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _))
    have hzint : Integrable (fun z : ℝ => z*f (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) := by
      apply ((HasExpGrowth.norm_id (E:=ℝ)).integrable_gaussianMeasure continuous_norm (μ:=gaussianReal 0 1) |>.mul_const B).mono'
        (continuous_id.mul hfc).aestronglyMeasurable
      exact ae_of_all _ (fun z => by simp only [Real.norm_eq_abs,Pi.mul_apply,id_eq,abs_mul]; exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _))
    have H := gaussian_integral_mul_eq_integral_deriv _ _ (fun z => by
      simpa only [mul_comm,Function.comp_def,Pi.sub_apply,id_eq,mul_one,one_mul,zero_sub] using (hd (Real.cos θ*y-Real.sin θ*z)).comp z
        ((hasDerivAt_const z (Real.cos θ*y)).sub ((hasDerivAt_id z).const_mul (Real.sin θ)))) hfint hdint hzint
    dsimp only [A,A',gaussianMix]
    simp only [neg_mul,← sub_eq_add_neg]
    calc
      _=k y*(∫ z : ℝ, z*f (Real.cos θ*y-Real.sin θ*z) ∂gaussianReal 0 1) := by
        rw [← integral_const_mul]; congr 1; funext z; ring
      _=k y*(∫ z : ℝ, -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z) ∂gaussianReal 0 1) := by rw [H]
      _=_ := by rw [integral_const_mul,integral_mul_const]; ring)

end SK.Analytic

end
end

end OAI
