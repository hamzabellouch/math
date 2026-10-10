import Mathlib
import OAI.Probability.SphericalField.Gaussian.Integration

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron
lemma standardGaussian_poincare {F D : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (D x) x)
    (hD : Continuous D) {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, |D x| ≤ C) :
    variance F (gaussianReal 0 1) ≤ (Real.pi^2/8)*(∫ x, (D x)^2 ∂gaussianReal 0 1) := by
  let γ := gaussianReal 0 1
  let μ := γ.prod γ
  let T := Real.pi/2
  let ν := volume.restrict (Ioc 0 T)
  let d := fun (t : ℝ) (p : ℝ×ℝ) =>
    D (Real.cos t*p.1+Real.sin t*p.2)*(-Real.sin t*p.1+Real.cos t*p.2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hν : ν.real univ = T := by simp [ν,Measure.real,Real.volume_Ioc,hT.le]
  have hdom (t : ℝ) (p : ℝ×ℝ) : (d t p)^2 ≤ 2*C^2*(p.1^2+p.2^2) := by
    have hb : |-Real.sin t*p.1+Real.cos t*p.2| ≤ |p.1|+|p.2| := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul,abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t,abs_nonneg p.1])
        (by nlinarith [Real.abs_cos_le_one t,abs_nonneg p.2])
    have hb2 : (-Real.sin t*p.1+Real.cos t*p.2)^2 ≤ 2*(p.1^2+p.2^2) := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ |p.1|+|p.2|)).mpr hb
      simp only [sq_abs] at hh
      nlinarith [sq_nonneg (|p.1|-|p.2|),sq_abs p.1,sq_abs p.2]
    have hD2 : (D (Real.cos t*p.1+Real.sin t*p.2))^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hDC _)
    dsimp only [d]
    rw [mul_pow]
    have hh := mul_le_mul hD2 hb2 (sq_nonneg _) (sq_nonneg C)
    nlinarith
  have hs : Integrable (fun x : ℝ => x^2) γ := (memLp_id_gaussianReal 2).integrable_sq
  have hdI : Integrable (fun p : (ℝ×ℝ)×ℝ => (d p.2 p.1)^2) (μ.prod ν) := by
    have hh : Integrable (fun p : (ℝ×ℝ)×ℝ => 2*C^2*(p.1.1^2+p.1.2^2)) (μ.prod ν) :=
      (((hs.comp_fst γ).add (hs.comp_snd γ)).const_mul (2*C^2)).comp_fst ν
    apply hh.mono' (by dsimp [d]; fun_prop)
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hdom p.2 p.1
  have hmF : MemLp F 2 γ := hasDerivAt_bounded_memLp hF hC hDC
  have hdiff : Integrable (fun p : ℝ×ℝ => (F p.2-F p.1)^2) μ := by
    simpa only [Pi.sub_apply] using ((hmF.comp_snd γ).sub (hmF.comp_fst γ)).integrable_sq
  have he : (∫ p : ℝ×ℝ, (F p.2-F p.1)^2 ∂μ) = 2*variance F γ := by
    rw [show (fun p : ℝ×ℝ => (F p.2-F p.1)^2) = fun p => (F p.1-F p.2)^2 by
      funext p; ring]
    exact integral_independent_difference_square γ hmF
  have hn := integral_mono_ae hdiff (hdI.integral_prod_left.const_mul T)
    (ae_of_all _ fun p => gaussian_rotation_path_bound hF hD p.1 p.2)
  rw [he,integral_const_mul,← integral_prod _ hdI,integral_prod_symm _ hdI] at hn
  have hmeans : (∫ t, ∫ p : ℝ×ℝ, (d t p)^2 ∂μ ∂ν) =
      T*(∫ x, (D x)^2 ∂γ) := by
    simp_rw [show ∀ t, (∫ p : ℝ×ℝ, (d t p)^2 ∂μ) = ∫ x, (D x)^2 ∂γ
      from fun t => gaussian_rotation_derivative_square_mean hD t]
    rw [integral_const,hν,smul_eq_mul]
  rw [hmeans] at hn
  dsimp only [T] at hn
  nlinarith

end SphericalPerceptron
end
end
end

end OAI
