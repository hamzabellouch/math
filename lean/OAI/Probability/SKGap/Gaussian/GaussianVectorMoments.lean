import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianQuadratic
import OAI.Probability.SKGap.Gaussian.GaussianRegression

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal

lemma gaussian_integral_fourth_variance (v : ℝ≥0) :
    (∫ x : ℝ,x^4 ∂gaussianReal 0 v)=3*(v:ℝ)^2 := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => sqrt (v:ℝ)*x)=gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hm,integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow,integral_const_mul,gaussian_integral_fourth]
  rw [show sqrt (v:ℝ)^4=(v:ℝ)^2 by rw [show 4=2*2 by norm_num,pow_mul,Real.sq_sqrt v.coe_nonneg]]
  ring

lemma gaussian_fourth_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq,norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 v) (4:ℝ≥0∞) (by norm_num)).integrable_norm_pow'

lemma linear_gaussian_fourth {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    (∫ g,(∑ i,a i*g i)^4 ∂gaussianCoordinates κ)=3*(∑ i,a i^2)^2 := by
  let A : Matrix Unit κ ℝ := fun _ => a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ → ℝ => ∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  have hm := linear_gaussian_mean a
  have hv : Var[fun g => ∑ i,a i*g i;gaussianCoordinates κ]=∑ i,a i^2 := by
    rw [← covariance_self hg.aemeasurable]
    simpa only [sq] using linear_gaussian_covariance a a
  change HasLaw (fun g : κ → ℝ => ∑ i,a i*g i) _ _ at hl
  rw [hm,hv] at hl
  have he := hl.integral_comp (f := fun x : ℝ => x^4) (by fun_prop)
  simp only [Function.comp_def] at he
  rw [he,gaussian_integral_fourth_variance]
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))]

lemma linear_gaussian_fourth_integrable {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    Integrable (fun g => (∑ i,a i*g i)^4) (gaussianCoordinates κ) := by
  let A : Matrix Unit κ ℝ := fun _ => a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ → ℝ => ∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  rw [linear_gaussian_mean a] at hl
  have hi := gaussian_fourth_integrable (Var[fun g : κ → ℝ => ∑ i,a i*g i;gaussianCoordinates κ].toNNReal)
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hl.aemeasurable).mp hi

end SKGap
end
end

end OAI
