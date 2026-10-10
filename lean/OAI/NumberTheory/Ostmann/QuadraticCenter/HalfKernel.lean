import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetProducts

namespace OAI

/-! # A small divisor carrying half the prime factors of a squarefree kernel -/

namespace Ostmann

open scoped BigOperators

private theorem exists_half_subset_product (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    ∃ U ⊆ P, U.card = P.card / 2 ∧ (∏ p ∈ U, p) ^ 2 ≤ ∏ p ∈ P, p := by
  classical
  let k := P.card / 2
  have hk : k ≤ P.card := Nat.div_le_self _ _
  obtain ⟨U₀, hU₀, hk₀⟩ := Finset.exists_subset_card_eq hk
  have hex : ∃ r : ℕ, ∃ U ⊆ P, U.card = k ∧ ∏ p ∈ U, p = r :=
    ⟨∏ p ∈ U₀, p, U₀, hU₀, hk₀, rfl⟩
  obtain ⟨U, hUP, hUk, hUr⟩ := Nat.find_spec hex
  have hcomp : k ≤ (P \ U).card := by
    rw [Finset.card_sdiff_of_subset hUP, hUk]
    dsimp [k]
    omega
  obtain ⟨V, hVP, hVk⟩ := Finset.exists_subset_card_eq hcomp
  have hmin : (∏ p ∈ U, p) ≤ ∏ p ∈ V, p := by
    rw [hUr]
    exact Nat.find_min' hex ⟨V, hVP.trans Finset.sdiff_subset, hVk, rfl⟩
  have hVPprod : (∏ p ∈ V, p) ≤ ∏ p ∈ P \ U, p := by
    exact Finset.prod_le_prod_of_subset_of_one_le₀ hVP (fun _ _ => Nat.zero_le _)
      (fun p hp _ => hP p (Finset.mem_sdiff.mp hp).1)
  have hprod : (∏ p ∈ U, p) * (∏ p ∈ P \ U, p) = ∏ p ∈ P, p := by
    rw [mul_comm, Finset.prod_sdiff hUP]
  refine ⟨U, hUP, hUk, ?_⟩
  calc
    _ = (∏ p ∈ U, p) * (∏ p ∈ U, p) := pow_two _
    _ ≤ (∏ p ∈ U, p) * (∏ p ∈ P \ U, p) := Nat.mul_le_mul_left _ (hmin.trans hVPprod)
    _ = _ := hprod

theorem squarefree_half_kernel (s : ℕ) (hs : Squarefree s) :
    ∃ r : ℕ, Squarefree r ∧ r ∣ s ∧ r ^ 2 ≤ s ∧
      r.primeFactors.card = s.primeFactors.card / 2 := by
  classical
  obtain ⟨U, hU, hcard, hprod⟩ := exists_half_subset_product s.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1.one_lt.le)
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (hU hp)).1
  have htotal := Nat.prod_primeFactors_of_squarefree hs
  refine ⟨∏ p ∈ U, p, primeSubset_product_squarefree U hprime, ?_, ?_, ?_⟩
  · refine ⟨∏ p ∈ s.primeFactors \ U, p, ?_⟩
    calc
      s = ∏ p ∈ s.primeFactors, p := htotal.symm
      _ = (∏ p ∈ U, p) * ∏ p ∈ s.primeFactors \ U, p := by
        rw [mul_comm, Finset.prod_sdiff hU]
  · rwa [htotal] at hprod
  · rw [Nat.primeFactors_prod hprime, hcard]

theorem half_kernel_weight (s r : ℕ) (hcard : r.primeFactors.card = s.primeFactors.card / 2)
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ s.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
  have hc : s.primeFactors.card ≤ 2 * r.primeFactors.card + 1 := by omega
  calc
    _ ≤ u ^ (2 * r.primeFactors.card + 1) := pow_le_pow_right₀ hu hc
    _ = _ := by rw [pow_add, pow_mul]; ring

noncomputable def smallHalfKernel (s : ℕ) : ℕ := by
  classical
  exact if h : Squarefree s then Classical.choose (squarefree_half_kernel s h) else 1

theorem smallHalfKernel_spec (s : ℕ) (hs : Squarefree s) :
    Squarefree (smallHalfKernel s) ∧ smallHalfKernel s ∣ s ∧ (smallHalfKernel s) ^ 2 ≤ s ∧
      (smallHalfKernel s).primeFactors.card = s.primeFactors.card / 2 := by
  classical
  simpa only [smallHalfKernel, dite_eq_left hs] using Classical.choose_spec (squarefree_half_kernel s hs)

end Ostmann

end OAI
