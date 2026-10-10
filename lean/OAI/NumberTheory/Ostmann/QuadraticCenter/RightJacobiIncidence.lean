import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiProducts

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem squarefree_factorization_indicator {n : ℕ} (hn : Squarefree n) (p : ℕ) :
    n.factorization p = if p ∈ n.primeFactors then 1 else 0 := by
  by_cases hp : p ∈ n.primeFactors
  · rw [ite_eq_left hp]
    obtain ⟨hpp, hpn, hn0⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.factorization_eq_one_of_squarefree hn hpp hpn
  · rw [ite_eq_right hp]
    exact Finsupp.notMem_support_iff.mp hp

theorem squarefree_product_isSquare_iff_even_incidence {κ : Type*} [Fintype κ]
    (n : κ → ℕ) (hn : ∀ i, Squarefree (n i)) :
    IsSquare (∏ i, n i) ↔
      ∀ p : ℕ, Even (∑ i, if p ∈ (n i).primeFactors then 1 else 0) := by
  classical
  have hfactor (p : ℕ) : (∏ i, n i).factorization p =
      ∑ i, if p ∈ (n i).primeFactors then 1 else 0 := by
    rw [Nat.factorization_prod_apply (fun i hi => (hn i).ne_zero)]
    apply Finset.sum_congr rfl
    intro i hi
    exact squarefree_factorization_indicator (hn i) p
  rw [Nat.isSquare_iff_even_factorization]
  constructor
  · intro h p
    rw [← hfactor]
    by_cases hp : p.Prime
    · exact h p hp
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact ⟨0, rfl⟩
  · intro h p hp
    rw [hfactor]
    exact h p

theorem squarefree_product_isSquare_iff_even_incidence_on {κ : Type*} [Fintype κ]
    (n : κ → ℕ) (hn : ∀ i, Squarefree (n i)) (P : Finset ℕ)
    (hP : ∀ i, (n i).primeFactors ⊆ P) :
    IsSquare (∏ i, n i) ↔
      ∀ p ∈ P, Even (∑ i, if p ∈ (n i).primeFactors then 1 else 0) := by
  rw [squarefree_product_isSquare_iff_even_incidence n hn]
  constructor
  · exact fun h p hp => h p
  · intro h p
    by_cases hp : p ∈ P
    · exact h p hp
    · have hnot : ∀ i, p ∉ (n i).primeFactors := fun i hi => hp (hP i hi)
      simp [hnot]

noncomputable def primeSupportWithin (P : Finset ℕ) (n : ℕ) : Finset P := by
  classical
  exact Finset.univ.filter (fun p : P => p.val ∈ n.primeFactors)

@[simp] theorem mem_primeSupportWithin {P : Finset ℕ} {n : ℕ} {p : P} :
    p ∈ primeSupportWithin P n ↔ p.val ∈ n.primeFactors := by
  classical
  simp only [primeSupportWithin, Finset.mem_filter, Finset.mem_univ, true_and]

theorem squarefree_product_isSquare_iff_even_primeSupportWithin {κ : Type*} [Fintype κ]
    (n : κ → ℕ) (hn : ∀ i, Squarefree (n i)) (P : Finset ℕ)
    (hP : ∀ i, (n i).primeFactors ⊆ P) :
    IsSquare (∏ i, n i) ↔
      ∀ p : P, Even (∑ i, if p ∈ primeSupportWithin P (n i) then 1 else 0) := by
  rw [squarefree_product_isSquare_iff_even_incidence_on n hn P hP]
  simp only [mem_primeSupportWithin, Subtype.forall]

theorem odd_jacobi_product_correlation_le_incidence {κ : Type*} [Fintype κ]
    (n : κ → ℕ) (hn : ∀ i, Squarefree (n i)) (P : Finset ℕ)
    (hP : ∀ i, (n i).primeFactors ⊆ P) (N : ℕ) :
    |∑ m ∈ (Finset.range N).filter Odd, ∏ i, (jacobiSym (n i : ℤ) m : ℝ)| ≤
      (N : ℝ) *
        (if ∀ p : P, Even (∑ i, if p ∈ primeSupportWithin P (n i) then 1 else 0) then 1 else 0) +
        4 * (∏ i, n i : ℕ) := by
  classical
  have hb := odd_jacobi_product_correlation_bound_real n
    (fun i => Nat.pos_of_ne_zero (hn i).ne_zero) N
  have he := squarefree_product_isSquare_iff_even_primeSupportWithin n hn P hP
  by_cases hs : IsSquare (∏ i, n i)
  · rw [ite_eq_left hs] at hb
    rw [ite_eq_left (he.mp hs), mul_one]
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · rw [ite_eq_right hs] at hb
    rw [ite_eq_right (fun h => hs (he.mpr h)), mul_zero, zero_add]
    exact hb

end Ostmann.QuadraticCenter

end OAI
