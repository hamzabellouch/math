import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantBounds
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCoprime

namespace OAI

/-! # The concrete frequency-model modulus in the bulk progression range -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingFrequencyModel_bulk_range (n k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (S : Finset ℤ) (N : ℕ) (t : FrequencyTree (S × S) n) (p : Fin m → ℕ),
      (∀ s ∈ S, s ≠ 0) → (∀ s ∈ S, s.natAbs ≤ N) →
      (N : ℝ) ≤ Real.exp (A * m) →
      (∀ i, (p i).Prime) → Function.Injective p → (∀ i, N < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let r := frequencyModelBase S n t ^ (n - 1 + 2)
      let M := ∏ i, bulkResidueModuli r p i
      0 < r ∧ 0 < M ∧
      Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)) ∧
      M ≤ bulkProgressionCutoff L := by
  let d : ℕ := 2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)
  filter_upwards [bulkResidueModulus_progression_range ((d : ℝ) * A) ((k : ℝ) ^ 4)
    (by positivity) (by positivity), eventually_ge_atTop (0 : ℝ)] with L hL hL0
  dsimp only
  intro S N t p hS hN hbound hp hinj hNp hupper
  let r := frequencyModelBase S n t ^ (n - 1 + 2)
  have hr : 0 < r := pow_pos (frequencyModelBase_pos S n t hS) _
  have hrbound : (r : ℝ) ≤ Real.exp (((d : ℝ) * A) * spectatorBulkCount k L) := by
    simpa only [d, r, mul_assoc] using frequencyModelModulus_exp_bound S N n t
      (A * spectatorBulkCount k L) hN hbound
  refine ⟨hr, bulkResidueModulus_positive r hr p (fun i => (hp i).pos), ?_,
    hL _ r p (spectatorBulkCount_upper k L hL0) hrbound hupper⟩
  apply bulkResidueModuli_pairwise r p hp hinj
  intro i
  exact ((prime_coprime_frequencyModelBase S N (p i) n (hp i) (hNp i)
    (fun s hs => ⟨hS s hs, hN s hs⟩) t).pow_right _).symm

end Ostmann

end OAI
