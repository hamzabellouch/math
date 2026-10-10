import Mathlib.Data.Nat.Factorization.Basic
import OAI.NumberTheory.Ostmann.Characters.RademacherMoments

namespace OAI

/-! # Identifying Boolean moments with square products of the actual indices -/

namespace Ostmann

open scoped BigOperators

private theorem squarefree_factorization_indicator {s : ℕ} (hs : Squarefree s) (p : ℕ) :
    s.factorization p = if p ∈ s.primeFactors then 1 else 0 := by
  classical
  by_cases hp : p ∈ s.primeFactors
  · rw [ite_eq_left hp]
    exact Nat.factorization_eq_one_of_squarefree hs (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  · rw [ite_eq_right hp]
    by_cases hprime : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hp (Nat.mem_primeFactors.mpr ⟨hprime, hd, hs.ne_zero⟩)
    · exact Nat.factorization_eq_zero_of_not_prime _ hprime

theorem squarefree_product_isSquare_iff {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (s : ι → ℕ) (hs : ∀ i, Squarefree (s i))
    (hP : ∀ i, (s i).primeFactors ⊆ P) :
    IsSquare (∏ i, s i) ↔ ∀ p : P,
      Even (monomialOccurrence (fun i => primeFactorSubset P (s i)) p) := by
  classical
  have he (p : ℕ) : (∏ i, s i).factorization p =
      ∑ i, if p ∈ (s i).primeFactors then 1 else 0 := by
    rw [Nat.factorization_prod (fun i _ => (hs i).ne_zero), Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact squarefree_factorization_indicator (hs i) p
  have hoc (p : P) : monomialOccurrence (fun i => primeFactorSubset P (s i)) p =
      (∏ i, s i).factorization p.val := by
    rw [he]
    simp only [monomialOccurrence, Finset.card_filter, mem_primeFactorSubset]
  rw [Nat.isSquare_iff_even_factorization]
  constructor
  · intro h p
    rw [hoc]
    by_cases hp : p.val.Prime
    · exact h p.val hp
    · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, Even.zero]
  · intro h p hp
    by_cases hpP : p ∈ P
    · simpa only [hoc] using h ⟨p, hpP⟩
    · rw [he]
      have hnot (i : ι) : p ∉ (s i).primeFactors := fun hh => hpP (hP i hh)
      simp only [hnot, ite_false, Finset.sum_const_zero, Even.zero]

theorem squarefree_diagonal_bonami (hB : PublishedBonamiBound) (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (a : S → ℝ) (l : ℕ) (hl : 0 < l) :
    (∑ t : Fin (2 * l) → S, (∏ j, a (t j)) *
      (if IsSquare (∏ j, (t j).val) then (1 : ℝ) else 0)) ≤
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * (a s) ^ 2) ^ l := by
  have he := rademacher_even_moment P (fun s : S => primeFactorSubset P s.val) a l
  have hi (t : Fin (2 * l) → S) :
      IsSquare (∏ j, (t j).val) ↔
        ∀ p : P, Even (monomialOccurrence (fun j => primeFactorSubset P (t j).val) p) :=
    squarefree_product_isSquare_iff P (fun j => (t j).val)
      (fun j => hS _ (t j).property) (fun j => hP _ (t j).property)
  simp_rw [← hi] at he
  rw [← he]
  exact bonami_squarefree_family hB P S hS hP a l hl

end Ostmann

end OAI
