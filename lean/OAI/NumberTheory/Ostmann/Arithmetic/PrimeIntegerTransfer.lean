import OAI.NumberTheory.Ostmann.Preliminaries.TransferCauchy
import OAI.NumberTheory.Ostmann.Construction.PrimePriorAtoms

namespace OAI

/-! # Extending the nonnegative transfer square from primes to integers -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_prior_integer_extension (S T : Finset ℕ) (hST : S ⊆ T)
    (w : ℝ → ℝ) (Z u : ℝ) (hZ : 0 ≤ Z) (hu : 0 ≤ u)
    (hpos : ∀ p ∈ S, p ≠ 0) (hw : ∀ n ∈ T, 0 ≤ w (Real.log n))
    (F : ℕ → ℝ) (hF : ∀ n ∈ T, 0 ≤ F n) :
    (∑ p : S, primeSamplePrior S w Z p * (((p : ℕ) : ℝ) * u * F p)) ≤
      Z * ∑ n ∈ T, w (Real.log n) * u * F n := by
  calc
    _ = ∑ p : S, Z * (w (Real.log (p : ℕ)) * u * F p) := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = (((p : ℕ) : ℝ) * primeSamplePrior S w Z p) * (u * F p) := by ring
        _ = _ := by rw [primeSamplePrior_value_mul S w Z p (hpos p p.property)]; ring
    _ = Z * ∑ n ∈ S, w (Real.log n) * u * F n := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort S (fun n : ℕ => w (Real.log n) * u * F n)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hST
        (fun n hn _ => mul_nonneg (mul_nonneg (hw n hn) hu) (hF n hn))) hZ

/-- This is the finite version of the prime-to-integer extension in
equation (53), using the original reciprocal-prime prior exactly. -/
theorem prime_integer_transfer_bound (S T : Finset ℕ) (hST : S ⊆ T)
    (w : ℝ → ℝ) (Z u : ℝ) (hZ : 0 ≤ Z) (hu : 0 ≤ u)
    (hpos : ∀ p ∈ S, p ≠ 0) (hw : ∀ n ∈ T, 0 ≤ w (Real.log n))
    (hmass : (∑ p : S, primeSamplePrior S w Z p) = 1)
    {A : S → Type*} [∀ p, Fintype (A p)]
    (row coefficient : ∀ p, A p → ℂ)
    (hrow : ∀ p : S, (∑ a, ‖row p a‖ ^ 2) ≤ ((p : ℕ) : ℝ) * u)
    (F : ℕ → ℝ) (hF : ∀ n ∈ T, 0 ≤ F n)
    (hcoeff : ∀ p : S, (∑ a, ‖coefficient p a‖ ^ 2) ≤ F p) :
    ‖∑ p : S, (primeSamplePrior S w Z p : ℂ) * ∑ a, row p a * coefficient p a‖ ^ 2 ≤
      Z * ∑ n ∈ T, w (Real.log n) * u * F n := by
  have hμ (p : S) : 0 ≤ primeSamplePrior S w Z p :=
    primeSamplePrior_nonneg S w Z hZ (fun p hp => hw p (hST hp)) p
  apply (finite_transfer_row_bound _ hμ hmass row coefficient _ hrow).trans
  apply le_trans _ (prime_prior_integer_extension S T hST w Z u hZ hu hpos hw F hF)
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hμ p)
  exact mul_le_mul_of_nonneg_left (hcoeff p) (mul_nonneg (Nat.cast_nonneg _) hu)

end Ostmann

end OAI
