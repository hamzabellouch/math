import OAI.NumberTheory.JointDickman.Amplification.GeometricFeatureBounds

namespace OAI

/-! # A bounded prime-site kernel has a bounded independent mean -/

namespace JointDickman
open Finset

theorem fullPrimeMass_total (P : Finset ℕ) : (∑ x, fullPrimeMass P x) = 1 :=
  bernoulliSiteMass_sum _

theorem primeKernel_mean_abs_le (B : ℕ)
    (K : (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ)
    {C : ℝ} (hK : ∀ x y, |K x y| ≤ C) :
    |∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*K x y| ≤ C := by
  let μ := fullPrimeMass (auxiliaryPrimes B)
  have hμ : ∀ x, 0 ≤ μ x := fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B)
  calc
    _ ≤ ∑ x, ∑ y, μ x*μ y*|K x y| := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro x _
      exact (abs_sum_le_sum_abs _ _).trans_eq (by
        apply sum_congr rfl
        intro y _
        rw [abs_mul,abs_of_nonneg (mul_nonneg (hμ x) (hμ y))])
    _ ≤ ∑ x, ∑ y, μ x*μ y*C := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hK x y) (mul_nonneg (hμ x) (hμ y))
    _ = C := by
      simp only [mul_assoc,← mul_sum,← sum_mul,μ,fullPrimeMass_total,one_mul]

end JointDickman

end OAI
