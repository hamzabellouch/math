import Mathlib.Data.Nat.GCD.BigOperators
import OAI.NumberTheory.Ostmann.Characters.SparseWeightGrowth

namespace OAI

/-! # Cardinality bound for the distinct selected primes -/
namespace Ostmann
open scoped Classical BigOperators

 theorem prime_family_injective {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hh := hc hij
  change (p i).Coprime (p j) at hh
  rw [he, Nat.coprime_self] at hh
  exact (Fact.out : (p j).Prime).ne_one hh

 theorem sparse_prime_family_card {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (L : ℝ) (hp : ∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) :
    (n : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) := by
  let R := Real.exp (Real.exp ((9 / 10 : ℝ) * L))
  have hsub : Finset.univ.image p ⊆ Finset.Icc 1 ⌊R⌋₊ := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_Icc.mpr ⟨(Fact.out : (p i).Prime).one_le, Nat.le_floor ?_⟩
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (Fact.out : (p i).Prime).pos)).mp (hp i)
  have hn : n ≤ ⌊R⌋₊ := by
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ (prime_family_injective p hc),
      Finset.card_univ, Fintype.card_fin, Nat.card_Icc, Nat.sub_zero, Nat.add_sub_cancel] using hh
  exact (Nat.cast_le.mpr hn).trans (Nat.floor_le (Real.exp_nonneg _))

end Ostmann

end OAI
