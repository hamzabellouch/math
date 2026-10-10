import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianCramer

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianHeat_abs_le {f : ℝ → ℝ} {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    (a x : ℝ) : |gaussianHeat a f x| ≤ B := by
  have H := norm_integral_le_of_norm_le (μ:=gaussianReal 0 1) (f:=fun z => f (x+a*z)) (integrable_const B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb (x+a*z)))
  simpa only [gaussianHeat,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using H

theorem gaussianHeat_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × ℝ => gaussianHeat p.1 f p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound:=fun _ : ℝ => B)
  · exact Eventually.of_forall (fun a => (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hb (a.2+a.1*z)))
  · exact integrable_const _
  · exact ae_of_all _ (fun z => (hf.comp (by fun_prop)).continuousAt)

theorem gaussianHeat_variance_integral_lower {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (a b c : ℝ) (he : c^2=b^2+a^2) :
    a^2*(∫ z, (gaussianHeat a df (b*z))^2 ∂gaussianReal 0 1) ≤
      (∫ z, f (c*z)^2 ∂gaussianReal 0 1)-
        (∫ z, (gaussianHeat a f (b*z))^2 ∂gaussianReal 0 1) := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hb2 (x : ℝ) : |f x^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)
  have hdheat := gaussianHeat_continuous hc hdf
  have hfheat := gaussianHeat_continuous hf hb
  have hf2heat := gaussianHeat_continuous (hf.pow 2) hb2
  have hi1 : Integrable (fun z => (gaussianHeat a df (b*z))^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hdheat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) hC (fun z => gaussianHeat_abs_le hdf a _)
  have hi2 : Integrable (fun z => gaussianHeat a (fun y => f y^2) (b*z)) (gaussianReal 0 1) :=
    gaussian_integrable_bounded (hf2heat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) (fun z => gaussianHeat_abs_le hb2 a _)
  have hi3 : Integrable (fun z => (gaussianHeat a f (b*z))^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hfheat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) hB (fun z => gaussianHeat_abs_le hb a _)
  have H := integral_mono (hi1.const_mul (a^2)) (hi2.sub hi3)
    (fun z => gaussianHeat_variance_lower hd hc hB hb hdf a (b*z))
  have HI := integral_sub hi2 hi3
  simp only [Pi.sub_apply] at H
  rw [integral_const_mul,HI] at H
  have HC := integral_gaussian_sum (hf.pow 2)
    (HasExpGrowth.of_bounded (sq_nonneg B) (fun x => by
      simpa only [Real.norm_eq_abs,Pi.pow_apply] using hb2 x)) b a c he
  change (∫ z, gaussianHeat a (fun y => f y^2) (b*z) ∂gaussianReal 0 1)=_ at HC
  rw [HC] at H
  exact H

theorem gaussianHeat_sq_average_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × ℝ => ∫ z, (gaussianHeat p.1 f (p.2*z))^2 ∂gaussianReal 0 1) := by
  have hh := gaussianHeat_continuous hf hb
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound:=fun _ : ℝ => B^2)
  · exact Eventually.of_forall (fun a => ((hh.comp (show Continuous (fun z : ℝ => (a.1,a.2*z)) by fun_prop)).pow 2).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (gaussianHeat_abs_le hb a.1 (a.2*z))))
  · exact integrable_const _
  · exact ae_of_all _ (fun z => ((hh.comp (show Continuous (fun a : ℝ × ℝ => (a.1,a.2*z)) by fun_prop)).pow 2).continuousAt)

end SK.Analytic

end
end

end OAI
