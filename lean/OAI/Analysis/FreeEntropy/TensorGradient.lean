import OAI.Analysis.FreeEntropy.MatrixBasisChart

namespace OAI

universe u1

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem realHermite_derivative_inner (n m : ℕ) :
    gaussianPolyIntegral ((realHermite n).derivative * (realHermite m).derivative) =
      (n : ℝ)*gaussianPolyIntegral (realHermite n*realHermite m) := by
  cases n with
  | zero => simp
  | succ n =>
    cases m with
    | zero => simp [realHermite_mean]
    | succ m =>
      rw [realHermite_derivative, realHermite_derivative, smul_mul_smul_comm,
        gaussianPolyIntegral_smul, realHermite_inner, realHermite_inner]
      by_cases h : n=m
      · subst m; simp [Nat.factorial_succ]; ring
      · simp [h]
 def tensorGradient (a : ι → ℕ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∏ j, (if j=i then (realHermite (a j)).derivative else realHermite (a j)).eval (x j)
 theorem tensorGradient_erase (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    tensorGradient a i x = (realHermite (a i)).derivative.eval (x i) *
      ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
  rw [tensorGradient, ← mul_prod_erase _ _ (mem_univ i)]
  simp only []
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [ite_eq_right (ne_of_mem_erase hj)]
 theorem tensorHermite_section (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    (fun t => tensorHermite a (Function.update x i t)) =
      fun t => (realHermite (a i)).eval t * ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
  funext t
  rw [tensorHermite, ← mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_erase hj)]
 theorem tensorHermite_hasDerivAt (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => tensorHermite a (Function.update x i t)) (tensorGradient a i x) (x i) := by
  rw [tensorHermite_section, tensorGradient_erase]
  exact ((realHermite (a i)).hasDerivAt (x i)).mul_const _
 theorem tensorGradient_integrable (a : ι → ℕ) (i : ι) :
    Integrable (tensorGradient a i) (productGaussian ι) :=
  Integrable.fintype_prod (fun _ => gaussian_polynomial_integrable 0 1 _)
 theorem tensorGradient_mul_integrable (a b : ι → ℕ) (i : ι) :
    Integrable (fun x => tensorGradient a i x * tensorGradient b i x) (productGaussian ι) := by
  have h := Integrable.fintype_prod (fun j => gaussian_polynomial_integrable 0 1
    ((if j=i then (realHermite (a j)).derivative else realHermite (a j)) *
      (if j=i then (realHermite (b j)).derivative else realHermite (b j))))
  simpa only [eval_mul, prod_mul_distrib, tensorGradient, productGaussian] using h
 theorem tensorGradient_inner (a b : ι → ℕ) (i : ι) :
    (∫ x, tensorGradient a i x*tensorGradient b i x ∂productGaussian ι) =
      if a=b then (a i : ℝ)*tensorWeight a else 0 := by
  have he : (∫ x, tensorGradient a i x*tensorGradient b i x ∂productGaussian ι) =
      (a i : ℝ) * ∫ x, tensorHermite a x*tensorHermite b x ∂productGaussian ι := by
    simp only [tensorGradient, tensorHermite, ← prod_mul_distrib, productGaussian]
    rw [integral_fintype_prod_eq_prod
      (fun j t => (if j=i then (realHermite (a j)).derivative else realHermite (a j)).eval t *
        (if j=i then (realHermite (b j)).derivative else realHermite (b j)).eval t),
      integral_fintype_prod_eq_prod
      (fun j t => (realHermite (a j)).eval t * (realHermite (b j)).eval t)]
    simp only [← eval_mul]
    change (∏ j, gaussianPolyIntegral ((if j=i then (realHermite (a j)).derivative else realHermite (a j)) *
      (if j=i then (realHermite (b j)).derivative else realHermite (b j)))) =
      (a i : ℝ) * ∏ j, gaussianPolyIntegral (realHermite (a j)*realHermite (b j))
    rw [← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase univ (fun j => gaussianPolyIntegral (realHermite (a j)*realHermite (b j))) (mem_univ i)]
    simp only [ite_true, realHermite_derivative_inner, mul_assoc]
    congr 2
    apply prod_congr rfl
    intro j hj
    simp only [ite_eq_right (ne_of_mem_erase hj)]
  rw [he, tensorHermite_inner]
  split_ifs <;> simp
end FiniteEntropySeparation

end

end OAI
