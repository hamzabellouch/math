import OAI.Analysis.FreeEntropy.GaussianHermite

namespace OAI

universe u1 u2

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def productGaussian (ι : Type u2) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
instance : IsProbabilityMeasure (productGaussian ι) := by unfold productGaussian; infer_instance

def tensorHermite (a : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, (realHermite (a i)).eval (x i)
def tensorWeight (a : ι → ℕ) : ℝ := ∏ i, (a i).factorial
@[simp] theorem tensorHermite_zero [DecidableEq ι] (x : ι → ℝ) : tensorHermite (fun _ => 0) x = 1 := by
  simp [tensorHermite]
theorem tensorHermite_integrable [DecidableEq ι] (a : ι → ℕ) : Integrable (tensorHermite a) (productGaussian ι) :=
  Integrable.fintype_prod (fun i => gaussian_polynomial_integrable 0 1 (realHermite (a i)))
theorem tensorHermite_mul_integrable [DecidableEq ι] (a b : ι → ℕ) :
    Integrable (fun x => tensorHermite a x * tensorHermite b x) (productGaussian ι) := by
  have h := Integrable.fintype_prod (fun i => gaussian_polynomial_integrable 0 1
    (realHermite (a i) * realHermite (b i)))
  simpa only [eval_mul, prod_mul_distrib, tensorHermite, productGaussian] using h
 theorem tensorHermite_mean [DecidableEq ι] (a : ι → ℕ) :
    (∫ x, tensorHermite a x ∂productGaussian ι) = if a=0 then 1 else 0 := by
  classical
  unfold tensorHermite productGaussian
  rw [integral_fintype_prod_eq_prod (fun i t => (realHermite (a i)).eval t)]
  change (∏ i, gaussianPolyIntegral (realHermite (a i))) = _
  simp_rw [realHermite_mean]
  by_cases ha : a=0
  · subst a; simp
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using ha
    apply prod_eq_zero (mem_univ i)
    simp [hi]
 theorem tensorHermite_inner [DecidableEq ι] (a b : ι → ℕ) :
    (∫ x, tensorHermite a x*tensorHermite b x ∂productGaussian ι) =
      if a=b then tensorWeight a else 0 := by
  classical
  simp only [tensorHermite, ← prod_mul_distrib]
  rw [productGaussian, integral_fintype_prod_eq_prod
    (fun i t => (realHermite (a i)).eval t * (realHermite (b i)).eval t)]
  simp only [← eval_mul]
  change (∏ i, gaussianPolyIntegral (realHermite (a i)*realHermite (b i))) = _
  simp_rw [realHermite_inner]
  by_cases ha : a=b
  · subst b; simp [tensorWeight]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by simpa only [funext_iff, not_forall] using ha
    apply prod_eq_zero (mem_univ i)
    simp [hi]
 theorem tensorWeight_pos [DecidableEq ι] (a : ι → ℕ) : 0 < tensorWeight a := by
  unfold tensorWeight
  exact prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (a i))
 theorem tensorHermite_update [DecidableEq ι] (a : ι → ℕ) (i : ι) (k : ℕ) (x : ι → ℝ) :
    tensorHermite (Function.update a i k) x = (realHermite k).eval (x i) *
      ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
  classical
  rw [tensorHermite, ← mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_erase hj)]
 theorem tensorHermite_mul_coord [DecidableEq ι] (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    x i * tensorHermite a x = tensorHermite (Function.update a i (a i+1)) x +
      (a i : ℝ) * tensorHermite (Function.update a i (a i-1)) x := by
  classical
  have he : tensorHermite a x = (realHermite (a i)).eval (x i) *
      ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
    simpa only [Function.update_eq_self] using tensorHermite_update a i (a i) x
  rw [he, tensorHermite_update, tensorHermite_update]
  have hr : x i * (realHermite (a i)).eval (x i) =
      (realHermite (a i+1)).eval (x i) + (a i : ℝ)*(realHermite (a i-1)).eval (x i) := by
    cases h : a i with
    | zero => simp [realHermite_succ]
    | succ n =>
      rw [realHermite_succ (n+1), realHermite_derivative]
      simp only [eval_sub, eval_mul, eval_X, eval_smul, smul_eq_mul, Nat.add_sub_cancel]
      push_cast
      ring
  rw [← mul_assoc, hr]
  ring
 def tensorHermiteSpan : Submodule ℝ ((ι → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (tensorHermite (ι := ι)))
 theorem tensorHermite_mem [DecidableEq ι] (a : ι → ℕ) : tensorHermite a ∈ tensorHermiteSpan :=
  Submodule.subset_span ⟨a,rfl⟩
 theorem tensorHermiteSpan_coord [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : f ∈ tensorHermiteSpan) (i : ι) :
    (fun x => x i*f x) ∈ tensorHermiteSpan := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,rfl⟩ := hf
    have hfun : (fun x => x i*tensorHermite a x) =
      tensorHermite (Function.update a i (a i+1)) + (a i : ℝ) • tensorHermite (Function.update a i (a i-1)) := by
      funext x; exact tensorHermite_mul_coord a i x
    rw [hfun]
    exact Submodule.add_mem _ (tensorHermite_mem _) (Submodule.smul_mem _ _ (tensorHermite_mem _))
  | zero =>
    convert (Submodule.zero_mem tensorHermiteSpan) using 1
    funext x; simp
  | add f g hf hg ihf ihg =>
    convert Submodule.add_mem tensorHermiteSpan ihf ihg using 1
    funext x; simp [mul_add]
  | smul r f hf ih =>
    convert Submodule.smul_mem tensorHermiteSpan r ih using 1
    funext x; simp [mul_left_comm]
 theorem mvPolynomial_hermite_span [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    (fun x => MvPolynomial.eval x P) ∈ tensorHermiteSpan := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    have he : (fun x : ι → ℝ => MvPolynomial.eval x (MvPolynomial.C r)) = r • tensorHermite (fun _ => 0) := by
      ext x; simp
    rw [he]; exact Submodule.smul_mem _ r (tensorHermite_mem _)
  | add P Q hP hQ =>
    convert Submodule.add_mem tensorHermiteSpan hP hQ using 1
    funext x; simp
  | mul_X P i hP => simpa only [map_mul, MvPolynomial.eval_X, mul_comm] using tensorHermiteSpan_coord hP i
 theorem mvPolynomial_hermite_expansion [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    ∃ a : (ι → ℕ) →₀ ℝ, (fun x => MvPolynomial.eval x P) = a.sum (fun k r => r • tensorHermite k) := by
  obtain ⟨a,ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (mvPolynomial_hermite_span P)
  exact ⟨a,ha.symm⟩
end FiniteEntropySeparation

end

end OAI
