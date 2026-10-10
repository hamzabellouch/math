import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

section
section
namespace MetricKMedian
namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem covariance_expansion (μ : FiniteLaw Ω) (X : Ω → I → ℝ) (q a b : I → ℝ)
    (hidem : ∀ ω i, X ω i * X ω i = X ω i)
    (hfirst : ∀ i, μ.expect (fun ω => X ω i) = q i)
    (hpair : ∀ i t, i ≠ t → μ.expect (fun ω => X ω i*X ω t) = q i*q t) :
    μ.expect (fun ω => (∑ i, a i*X ω i)*(∑ t, b t*X ω t)) =
      (∑ i, a i*q i)*(∑ t, b t*q t)+∑ i, a i*b i*q i*(1-q i) := by
  have hcov : ∀ i t, μ.expect (fun ω => X ω i*X ω t) =
      q i*q t+(if i=t then q i*(1-q i) else 0) := by
    intro i t
    by_cases hit : i=t
    · subst t
      simp_rw [hidem]
      rw [hfirst, ite_true]
      ring
    · rw [hpair i t hit, ite_eq_right hit, add_zero]
  have hprod : ∀ ω, (∑ i, a i*X ω i)*(∑ t, b t*X ω t) =
      ∑ i, ∑ t, (a i*b t)*(X ω i*X ω t) := by
    intro ω
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [hprod, μ.expect_sum, μ.expect_mul, hcov, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_zero]
  have hdiag : (∑ i, ∑ t, if i=t then a i*b t*(q i*(1-q i)) else 0) =
      ∑ i, a i*b i*q i*(1-q i) := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag]
  congr 1
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  ring

end FiniteLaw

namespace GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

noncomputable def removedMass (g : ℝ) (X : Ω → H → I → ℝ) (ω : Ω) (h : H) : ℝ :=
  ∑ i, g*X ω h i
noncomputable def removedCost (g : ℝ) (d : I → ℝ) (X : Ω → H → I → ℝ)
    (ω : Ω) (h : H) : ℝ := ∑ i, g*d i*X ω h i
noncomputable def kernel (g : ℝ) (q : H → I → ℝ) (i t : I) : ℝ :=
  ∑ h, g*q h i*q h t

theorem quadratic_identity (μ : FiniteLaw Ω) (g : ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hidem : ∀ ω h i, X ω h i*X ω h i = X ω h i)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i) = q h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => X ω h i*X ω h t) = q h i*q h t) :
    μ.expect (fun ω => ∑ h, g*removedMass g X ω h*removedCost g d X ω h) =
      (∑ i, ∑ t, g^2*kernel g q i t*d t)+
      ∑ i, g^2*d i*∑ h, g*q h i*(1-q h i) := by
  have hsource : ∀ h, μ.expect (fun ω =>
      g*removedMass g X ω h*removedCost g d X ω h) =
      (∑ i, ∑ t, g^3*q h i*q h t*d t)+
      ∑ i, g^3*d i*q h i*(1-q h i) := by
    intro h
    rw [show (fun ω => g*removedMass g X ω h*removedCost g d X ω h) =
        (fun ω => g*((∑ i, g*X ω h i)*(∑ t, (g*d t)*X ω h t))) by
      funext ω; dsimp only [removedMass, removedCost]; ring]
    rw [μ.expect_mul, μ.covariance_expansion (fun ω => X ω h) (q h) (fun _ => g)
      (fun i => g*d i) (fun ω i => hidem ω h i) (hfirst h) (hpair h)]
    rw [mul_add, Finset.sum_mul]
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [μ.expect_sum]
  simp_rw [hsource, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [kernel, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring

omit [DecidableEq I] in
                                                                              
theorem diagonal_bound {g : ℝ} (hg : 0 ≤ g) (d : I → ℝ) (q : H → I → ℝ)
    (hd : ∀ i, 0 ≤ d i)
    (hincoming : ∀ i, ∑ h, g*q h i ≤ 1) :
    (∑ i, g^2*d i*∑ h, g*q h i*(1-q h i)) ≤ g*(∑ i, g*d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hinner : (∑ h, g*q h i*(1-q h i)) ≤ 1 := by
    apply le_trans _ (hincoming i)
    apply Finset.sum_le_sum
    intro h _
    nlinarith only [mul_nonneg hg (sq_nonneg (q h i))]
  have hh := mul_le_mul_of_nonneg_left hinner (mul_nonneg (sq_nonneg g) (hd i))
  nlinarith only [hh]

end GraphMoments
end MetricKMedian
end
end

end OAI
