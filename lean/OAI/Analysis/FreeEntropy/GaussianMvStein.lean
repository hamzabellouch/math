import OAI.Analysis.FreeEntropy.TensorPoincare

namespace OAI

universe u1

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem tensorHermite_coord_eq (a : ι → ℕ) (i : ι) :
    (fun x => x i*tensorHermite a x) =
      fun x => ∏ j, (if j=i then Polynomial.X*realHermite (a j) else realHermite (a j)).eval (x j) := by
  funext x
  rw [← mul_prod_erase univ _ (mem_univ i)]
  have hh : tensorHermite a x = (realHermite (a i)).eval (x i)*∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
    simpa only [Function.update_eq_self] using tensorHermite_update a i (a i) x
  rw [hh]
  simp only [ite_true, Polynomial.eval_mul, Polynomial.eval_X, mul_assoc]
  congr 2
  apply prod_congr rfl
  intro j hj
  rw [ite_eq_right (ne_of_mem_erase hj)]
 theorem tensorHermite_coord_integrable (a : ι → ℕ) (i : ι) :
    Integrable (fun x => x i*tensorHermite a x) (productGaussian ι) := by
  rw [tensorHermite_coord_eq]
  exact Integrable.fintype_prod (fun j => gaussian_polynomial_integrable 0 1 _)
 theorem tensorHermite_stein (a : ι → ℕ) (i : ι) :
    (∫ x, x i*tensorHermite a x ∂productGaussian ι) = ∫ x, tensorGradient a i x ∂productGaussian ι := by
  rw [tensorHermite_coord_eq]
  unfold tensorGradient productGaussian
  rw [integral_fintype_prod_eq_prod (fun j t => (if j=i then Polynomial.X*realHermite (a j) else realHermite (a j)).eval t),
    integral_fintype_prod_eq_prod (fun j t => (if j=i then (realHermite (a j)).derivative else realHermite (a j)).eval t)]
  apply prod_congr rfl
  intro j hj
  by_cases h : j=i
  · subst j
    simpa only [ite_true, Polynomial.eval_mul, Polynomial.eval_X] using gaussian_polynomial_stein (realHermite (a i))
  · simp [h]
 theorem linearExpand_coord {ι : Type u1} [Fintype ι] [DecidableEq ι] (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    (fun x => x i*linearExpand tensorHermite a x) = linearExpand (fun k x => x i*tensorHermite k x) a := by
  funext x
  simp only [linearExpand_apply, mul_sum]
  apply sum_congr rfl
  intro k hk
  ring
 theorem tensorExpansion_stein (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    (∫ x, x i*linearExpand tensorHermite a x ∂productGaussian ι) =
      ∫ x, coordinateDerivative (linearExpand tensorHermite a) i x ∂productGaussian ι := by
  rw [linearExpand_coord, tensorExpansion_derivative,
    linearExpand_integral (fun k => tensorHermite_coord_integrable k i),
    linearExpand_integral (fun k => tensorGradient_integrable k i)]
  simp_rw [tensorHermite_stein]
 theorem gaussian_mvPolynomial_stein (P : MvPolynomial ι ℝ) (i : ι) :
    (∫ x, x i*MvPolynomial.eval x P ∂productGaussian ι) =
      ∫ x, coordinateDerivative (fun y => MvPolynomial.eval y P) i x ∂productGaussian ι := by
  obtain ⟨a,ha⟩ := mvPolynomial_hermite_expansion P
  change (fun x => MvPolynomial.eval x P) = linearExpand tensorHermite a at ha
  simpa only [← ha] using tensorExpansion_stein a i
end FiniteEntropySeparation

end

end OAI
