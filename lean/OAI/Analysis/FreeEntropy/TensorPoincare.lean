import OAI.Analysis.FreeEntropy.OrthogonalExpansion

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def coordinateDerivative (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)
 theorem tensorExpansion_hasDerivAt (a : (ι → ℕ) →₀ ℝ) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => linearExpand tensorHermite a (Function.update x i t))
      (linearExpand (fun k => tensorGradient k i) a x) (x i) := by
  simp only [linearExpand_apply]
  exact HasDerivAt.fun_sum (fun k _ => (tensorHermite_hasDerivAt k i x).const_mul (a k))
 theorem tensorExpansion_derivative (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    coordinateDerivative (linearExpand tensorHermite a) i = linearExpand (fun k => tensorGradient k i) a := by
  funext x
  exact (tensorExpansion_hasDerivAt a i x).deriv
 theorem tensorExpansion_mean (a : (ι → ℕ) →₀ ℝ) :
    (∫ x, linearExpand tensorHermite a x ∂productGaussian ι) = a 0 := by
  rw [linearExpand_integral tensorHermite_integrable]
  simp_rw [tensorHermite_mean]
  simp_all
 theorem tensorExpansion_energy (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    (∫ x, (coordinateDerivative (linearExpand tensorHermite a) i x)^2 ∂productGaussian ι) =
      ∑ k ∈ a.support, (k i : ℝ)*(a k)^2*tensorWeight k := by
  rw [tensorExpansion_derivative]
  simp only [pow_two]
  rw [linearExpand_orthogonal (fun k l => tensorGradient_mul_integrable k l i)
    (fun k => (k i : ℝ)*tensorWeight k) (fun k l => tensorGradient_inner k l i)]
  apply sum_congr rfl
  intro k hk
  ring
 theorem tensorExpansion_variance (a : (ι → ℕ) →₀ ℝ) :
    (∫ x, (linearExpand tensorHermite a x - ∫ y, linearExpand tensorHermite a y ∂productGaussian ι)^2
      ∂productGaussian ι) = (∑ k ∈ a.support, (a k)^2*tensorWeight k) - (a 0)^2 := by
  rw [integral_center_sq (linearExpand_integrable tensorHermite_integrable _)
    (linearExpand_mul_integrable tensorHermite_mul_integrable _ _),
    linearExpand_orthogonal tensorHermite_mul_integrable tensorWeight tensorHermite_inner,
    tensorExpansion_mean]
  simp only [pow_two]
 theorem tensorDegree_ge_one {ι : Type u1} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (hk : k ≠ 0) : (1 : ℝ) ≤ ∑ i, (k i : ℝ) := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    apply hk
    funext i
    by_contra hi
    exact h ⟨i,hi⟩
  calc
    (1 : ℝ) ≤ k i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
    _ ≤ ∑ j, (k j : ℝ) := single_le_sum (f := fun j => (k j : ℝ)) (fun j _ => by positivity) (mem_univ i)
 theorem tensorExpansion_poincare (a : (ι → ℕ) →₀ ℝ) :
    (∫ x, (linearExpand tensorHermite a x - ∫ y, linearExpand tensorHermite a y ∂productGaussian ι)^2
      ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative (linearExpand tensorHermite a) i x)^2 ∂productGaussian ι := by
  classical
  rw [tensorExpansion_variance]
  simp_rw [tensorExpansion_energy]
  rw [sum_comm]
  have hz : (a 0)^2 = ∑ k ∈ a.support, if k=0 then (a k)^2 else 0 := by simp
  rw [hz, ← sum_sub_distrib]
  apply sum_le_sum
  intro k hk
  by_cases hk0 : k=0
  · subst k; simp [tensorWeight]
  · rw [ite_eq_right hk0, sub_zero]
    simp only [← sum_mul]
    have hd := tensorDegree_ge_one hk0
    have hw : 0 ≤ (a k)^2*tensorWeight k := mul_nonneg (sq_nonneg _) (tensorWeight_pos k).le
    nlinarith

 theorem gaussian_mvPolynomial_poincare (P : MvPolynomial ι ℝ) :
    (∫ x, (MvPolynomial.eval x P - ∫ y, MvPolynomial.eval y P ∂productGaussian ι)^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative (fun y => MvPolynomial.eval y P) i x)^2 ∂productGaussian ι := by
  obtain ⟨a,ha⟩ := mvPolynomial_hermite_expansion P
  change (fun x => MvPolynomial.eval x P) = linearExpand tensorHermite a at ha
  simpa only [← ha] using tensorExpansion_poincare a
 theorem gaussian_mvPolynomial_integrable (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P) (productGaussian ι) := by
  obtain ⟨a,ha⟩ := mvPolynomial_hermite_expansion P
  change (fun x => MvPolynomial.eval x P) = linearExpand tensorHermite a at ha
  rw [ha]
  exact linearExpand_integrable tensorHermite_integrable a
end FiniteEntropySeparation

end

end OAI
