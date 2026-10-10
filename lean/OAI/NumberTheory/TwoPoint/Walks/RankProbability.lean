import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

namespace OAI

/-!
# Arithmetic and zero-set estimates for random prime controls

A nonzero integer has few distinct prime divisors. Bounds for joint
zero-coordinate events then control the probability that independent
prime coordinates divide every entry of a random integral vector.
-/

namespace TwoPointCorrelations

open Finset

lemma card_primeFactors_le_log_two (n : ℕ) (hn : n ≠ 0) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc
    2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
      pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

lemma card_prime_divisors_le_log (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℤ) (hz : z ≠ 0) :
    (P.filter (fun p : ℕ => (p : ℤ) ∣ z)).card ≤ Nat.log 2 z.natAbs := by
  apply (card_le_card ?_).trans (card_primeFactors_le_log_two _ (by simpa using hz))
  intro p hp
  obtain ⟨hp, hd⟩ := mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hP p hp, Int.natCast_dvd.mp hd, by simpa using hz⟩

namespace FiniteLaw

/-- A nonzero integer can be hit only by its distinct prime divisors. -/
lemma prime_divisibility_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : FiniteLaw P) (α : ℝ) (hα : 0 ≤ α) (hμ : ∀ p, μ.weight p ≤ α)
    (z : ℤ) (hz : z ≠ 0) :
    μ.probability (fun p => (p.val : ℤ) ∣ z) ≤ α * (Nat.log 2 z.natAbs : ℝ) := by
  classical
  let S : Finset P := univ.filter (fun p => (p.val : ℤ) ∣ z)
  have hc : S.card ≤ Nat.log 2 z.natAbs := by
    apply (card_le_card_of_injOn (fun p : P => p.val) ?_ ?_).trans
      (card_prime_divisors_le_log P hP z hz)
    · intro p hp
      exact mem_filter.mpr ⟨p.property, (mem_filter.mp hp).2⟩
    · intro p _ q _ hpq
      exact Subtype.ext hpq
  have heq : μ.probability (fun p => (p.val : ℤ) ∣ z) = ∑ p ∈ S, μ.weight p := by
    simp [probability, average, S, sum_filter]
  rw [heq]
  calc
    ∑ p ∈ S, μ.weight p ≤ ∑ _p ∈ S, α := sum_le_sum (fun p _ => hμ p)
    _ = α * S.card := by simp [mul_comm]
    _ ≤ α * (Nat.log 2 z.natAbs : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hα

/-- Expanding by zero-coordinate subsets converts joint zero estimates
into a product estimate. This does not require independence of the zero
events. -/
theorem zero_set_product_bound {Y ι : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι]
    (μ : FiniteLaw Y) (v : Y → ι → ℤ) (α β : ℝ) (hβ : 0 ≤ β)
    (hzero : ∀ S : Finset ι,
      μ.average (fun y => ∏ i ∈ S, if v y i = 0 then (1 : ℝ) else 0) ≤ α ^ S.card) :
    μ.average (fun y => ∏ i, if v y i = 0 then (1 : ℝ) else β) ≤
      (α + β) ^ Fintype.card ι := by
  classical
  calc
    _ ≤ μ.average (fun y => ∏ i, ((if v y i = 0 then (1 : ℝ) else 0) + β)) := by
      apply μ.average_mono
      intro y
      apply prod_le_prod₀
      · intro i _
        split_ifs <;> positivity
      · intro i _
        split_ifs <;> linarith
    _ = ∑ S : Finset ι, μ.average (fun y =>
        (∏ i ∈ S, if v y i = 0 then (1 : ℝ) else 0) * β ^ Sᶜ.card) := by
      simp_rw [Fintype.prod_add, prod_const]
      exact μ.average_sum _
    _ ≤ ∑ S : Finset ι, α ^ S.card * β ^ Sᶜ.card := by
      apply sum_le_sum
      intro S _
      rw [μ.average_mul_const]
      exact mul_le_mul_of_nonneg_right (hzero S) (pow_nonneg hβ _)
    _ = (α + β) ^ Fintype.card ι := by
      simpa only [prod_const, card_univ] using
        (Fintype.prod_add (fun _ : ι => α) (fun _ : ι => β)).symm

end FiniteLaw

end TwoPointCorrelations

end OAI
