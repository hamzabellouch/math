import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedPrior

namespace OAI

/-! # Disjoint prime cells force every nonzero matching to preserve its cell -/

namespace Ostmann
open scoped Classical BigOperators

theorem matched_prior_preserves_cell {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (e : Equiv.Perm H) (x : H → P)
    (hx : (∏ i, primeSubsetPrior P (Q i) (x i)) ≠ 0)
    (he : (∏ i, primeSubsetPrior P (Q i) (x (e i))) ≠ 0) :
    ∀ i, label (e i) = label i := by
  intro i
  by_contra hn
  have h₁ : (x (e i) : ℕ) ∈ Q (e i) := primeSubsetPrior_support P _ _
    ((Finset.prod_ne_zero_iff.mp hx) (e i) (Finset.mem_univ _))
  have h₂ : (x (e i) : ℕ) ∈ Q i := primeSubsetPrior_support P _ _
    ((Finset.prod_ne_zero_iff.mp he) i (Finset.mem_univ _))
  exact Finset.disjoint_left.mp (hdisjoint (e i) i hn) h₁ h₂

theorem matched_prior_zero_of_changes_cell {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (e : Equiv.Perm H) (hchange : ∃ i, label (e i) ≠ label i)
    (x : H → P) :
    (∏ i, primeSubsetPrior P (Q i) (x i)) *
      (∏ i, primeSubsetPrior P (Q i) (x (e i))) = 0 := by
  by_contra hn
  have h := mul_ne_zero_iff.mp hn
  obtain ⟨i, hi⟩ := hchange
  exact hi (matched_prior_preserves_cell P Q label hdisjoint e x h.1 h.2 i)

theorem matched_correlation_zero_of_changes_cell {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K)
    (hdisjoint : ∀ i j, label i ≠ label j → Disjoint (Q i) (Q j))
    (e : Equiv.Perm H) (hchange : ∃ i, label (e i) ≠ label i)
    (F : (H → P) → ℂ) :
    (∑ x : H → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ i, primeSubsetPrior P (Q i) (x (e i)) : ℝ) : ℂ) * F x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rw [← Complex.ofReal_mul, matched_prior_zero_of_changes_cell P Q label hdisjoint e hchange x,
    Complex.ofReal_zero, zero_mul]

/-- The same conclusion uses the actual prime-cell labeling directly. -/
theorem matched_prior_preserves_prime_label {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K) (cell : ℕ → K)
    (hsupport : ∀ i p, p ∈ Q i → cell p = label i)
    (e : Equiv.Perm H) (x : H → P)
    (hx : (∏ i, primeSubsetPrior P (Q i) (x i)) ≠ 0)
    (he : (∏ i, primeSubsetPrior P (Q i) (x (e i))) ≠ 0) :
    ∀ i, label (e i) = label i := by
  apply matched_prior_preserves_cell P Q label _ e x hx he
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hi hj
  exact hij ((hsupport i p hi).symm.trans (hsupport j p hj))

theorem matched_correlation_zero_of_changes_prime_label {H K : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (label : H → K) (cell : ℕ → K)
    (hsupport : ∀ i p, p ∈ Q i → cell p = label i)
    (e : Equiv.Perm H) (hchange : ∃ i, label (e i) ≠ label i)
    (F : (H → P) → ℂ) :
    (∑ x : H → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ i, primeSubsetPrior P (Q i) (x (e i)) : ℝ) : ℂ) * F x) = 0 := by
  apply matched_correlation_zero_of_changes_cell P Q label _ e hchange F
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hi hj
  exact hij ((hsupport i p hi).symm.trans (hsupport j p hj))

end Ostmann

end OAI
