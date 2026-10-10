import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentSupport

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

noncomputable def cutoffPrimeJacobi {P : Finset ℕ} (B m : ℕ) (s : Finset P) : ℝ :=
  if primeSubsetProduct s ≤ B then (jacobiSym (primeSubsetProduct s : ℤ) m : ℝ) else 0

theorem cutoffPrimeJacobi_correlation {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (B N k : ℕ) (f : Fin k → Finset P) :
    |∑ m ∈ (Finset.range N).filter Odd, ∏ j, cutoffPrimeJacobi B m (f j)| ≤
      (N : ℝ) * (if ∀ p : P, Even (∑ j, if p ∈ f j then 1 else 0) then 1 else 0) +
        4 * (B : ℝ) ^ k := by
  classical
  by_cases hf : ∀ j, primeSubsetProduct (f j) ≤ B
  · have heq (m : ℕ) (j : Fin k) : cutoffPrimeJacobi B m (f j) =
        (jacobiSym (primeSubsetProduct (f j) : ℤ) m : ℝ) := by
      simp only [cutoffPrimeJacobi, ite_eq_left (hf j)]
    simp only [heq]
    have hcor := odd_jacobi_product_correlation_le_incidence
      (fun j => primeSubsetProduct (f j))
      (fun j => primeSubsetProduct_squarefree hP (f j)) P
      (fun j => primeSubsetProduct_primeFactors_subset hP (f j)) N
    simp only [primeSupportWithin_primeSubsetProduct hP] at hcor
    apply hcor.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hprod : (∏ j, primeSubsetProduct (f j)) ≤ B ^ k := by
      calc
        (∏ j, primeSubsetProduct (f j)) ≤ ∏ _j : Fin k, B :=
          Finset.prod_le_prod (fun j hj => hf j)
        _ = B ^ k := by simp
    exact_mod_cast hprod
  · push Not at hf
    obtain ⟨j, hj⟩ := hf
    have hz (m : ℕ) : (∏ i, cutoffPrimeJacobi B m (f i)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [cutoffPrimeJacobi, ite_eq_right (not_le.mpr hj)]
    simp only [hz, Finset.sum_const_zero, abs_zero]
    positivity

end Ostmann.QuadraticCenter

end OAI
