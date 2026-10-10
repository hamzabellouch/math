import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRegression

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators

lemma linear_gaussian_law {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    HasLaw (fun g : κ→ℝ=>∑ i,a i*g i) (gaussianReal 0 (∑ i,a i^2).toNNReal)
      (gaussianCoordinates κ) := by
  let A : Matrix Unit κ ℝ := fun _=>a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ→ℝ=>∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  have hm := linear_gaussian_mean a
  have hv : Var[fun g=>∑ i,a i*g i;gaussianCoordinates κ]=∑ i,a i^2 := by
    rw [← covariance_self hg.aemeasurable]
    simpa only [sq] using linear_gaussian_covariance a a
  change HasLaw (fun g : κ→ℝ=>∑ i,a i*g i) _ _ at hl
  rw [hm,hv] at hl
  exact hl

lemma linear_gaussian_exp_integrable {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    Integrable (fun g : κ→ℝ=>exp (∑ i,a i*g i)) (gaussianCoordinates κ) := by
  have hl := linear_gaussian_law a
  have hi : Integrable exp (gaussianReal 0 (∑ i,a i^2).toNNReal) := by
    simpa using (integrable_exp_mul_gaussianReal (μ:=0) (v:=(∑ i,a i^2).toNNReal) 1)
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hl.aemeasurable).mp hi

lemma linear_gaussian_exp_integral {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    (∫ g : κ→ℝ,exp (∑ i,a i*g i) ∂gaussianCoordinates κ)=exp ((∑ i,a i^2)/2) := by
  have hl := linear_gaussian_law a
  have he := mgf_gaussianReal hl 1
  simpa only [mgf,one_mul,zero_mul,one_pow,mul_one,zero_add,
    coe_toNNReal _ (Finset.sum_nonneg (fun i _=>sq_nonneg (a i)))] using he

end SKGap
end
end

end OAI
