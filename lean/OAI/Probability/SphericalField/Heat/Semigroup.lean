import Mathlib
import OAI.Probability.SphericalField.Heat.Entropic

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledStdGaussian (σ : ℝ) : Measure E := (stdGaussian E).map (σ • ·)

instance (σ : ℝ) : IsProbabilityMeasure (scaledStdGaussian (E := E) σ) :=
  inferInstanceAs (IsProbabilityMeasure ((stdGaussian E).map (σ • ·)))

lemma scaledStdGaussian_conv (σ τ : ℝ) :
    (scaledStdGaussian (E := E) σ) ∗ (scaledStdGaussian τ)=
      scaledStdGaussian (Real.sqrt (σ^2+τ^2)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv]
  simp only [scaledStdGaussian,charFun_map_smul,charFun_stdGaussian]
  rw [← Complex.exp_add]
  congr 1
  have hr : -‖σ • t‖^2/2 + -‖τ • t‖^2/2 = -‖Real.sqrt (σ^2+τ^2) • t‖^2/2 := by
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      Real.sq_sqrt (add_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    ring
  exact_mod_cast hr

lemma stdGaussian_integral_add {F : E → ℝ} (hF : Continuous F) (σ τ : ℝ)
    (hI : Integrable (fun y : E => F (Real.sqrt (σ^2+τ^2) • y)) (stdGaussian E)) :
    (∫ y, ∫ z, F (σ • y+τ • z) ∂stdGaussian E ∂stdGaussian E)=
      ∫ y, F (Real.sqrt (σ^2+τ^2) • y) ∂stdGaussian E := by
  have hi : Integrable F (scaledStdGaussian (E := E) (Real.sqrt (σ^2+τ^2))) := by
    exact (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mpr hI
  rw [← scaledStdGaussian_conv σ τ] at hi
  have H := integral_conv hi
  rw [scaledStdGaussian_conv σ τ] at H
  simp only [scaledStdGaussian] at H
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable] at H
  have hm : StronglyMeasurable (fun y : E => ∫ z : E, F (y+z) ∂(stdGaussian E).map (τ • ·)) :=
    ((hF.comp (continuous_fst.add continuous_snd)).stronglyMeasurable).integral_prod_right'
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable] at H
  have HH : ∀ y : E, (∫ z, F (σ • y+z) ∂(stdGaussian E).map (τ • ·))=
      ∫ z, F (σ • y+τ • z) ∂stdGaussian E := by
    intro y
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [HH] at H
  exact H.symm

lemma gaussianEntropic_semigroup {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p : ℝ} (hp : 0 ≤ p) (σ τ : ℝ) (x : E) :
    gaussianEntropic (stdGaussian E) p σ (gaussianEntropic (stdGaussian E) p τ f) x=
      gaussianEntropic (stdGaussian E) p (Real.sqrt (σ^2+τ^2)) f x := by
  have hfc := hf.continuous
  have hinner := gaussianEntropic_lipschitz (stdGaussian E) hf (σ := τ) hp
  by_cases hp0 : p=0
  · subst p
    rw [gaussianEntropic_zero _ hinner,gaussianEntropic_zero _ hf]
    simp_rw [gaussianEntropic_zero _ hf]
    have H := stdGaussian_integral_add (F := fun y => f (x+y)) (by fun_prop) σ τ
      (gaussian_integrable_lipschitz (stdGaussian E) hf _ x)
    simpa only [add_assoc] using H
  · rw [gaussianEntropic_pos _ hinner hp0,gaussianEntropic_pos _ hf hp0]
    have he (y : E) : Real.exp (p*gaussianEntropic (stdGaussian E) p τ f (x+σ • y))=
        ∫ z, Real.exp (p*f (x+σ • y+τ • z)) ∂stdGaussian E := by
      rw [gaussianEntropic_pos _ hf hp0]
      rw [mul_div_cancel₀ _ hp0]
      apply Real.exp_log
      exact mgf_pos (gaussian_integrable_exp_lipschitz (stdGaussian E) hf p τ _)
    simp_rw [he]
    have H := stdGaussian_integral_add (F := fun y => Real.exp (p*f (x+y))) (by fun_prop) σ τ
      (gaussian_integrable_exp_lipschitz (stdGaussian E) hf p _ x)
    simpa only [add_assoc] using congrArg (fun a : ℝ => Real.log a/p) H

lemma gaussianEntropic_variance_zero {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (p : ℝ) (x : E) :
    gaussianEntropic (stdGaussian E) p 0 f x=f x := by
  by_cases hp : p=0
  · subst p
    simp [gaussianEntropic_zero _ hf]
  · rw [gaussianEntropic_pos _ hf hp]
    simp [hp]

end
end SphericalPerceptron
end
end

end OAI
