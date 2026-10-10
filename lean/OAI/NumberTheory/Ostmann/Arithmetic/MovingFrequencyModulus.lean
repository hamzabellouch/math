import OAI.NumberTheory.Ostmann.Arithmetic.MovingUnitPeriodBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCoprime

namespace OAI

/-! # The concrete frequency modulus for the original pair of histories -/

namespace Ostmann
open scoped Classical

def movingPairFrequencyBase {σ : Type*} {n : ℕ} (T : Bool → MovingSlotData σ n) : ℤ :=
  (T false).frequencyProduct * (T true).frequencyProduct

def movingPairFrequencyModulus {σ : Type*} {n : ℕ} (T : Bool → MovingSlotData σ n) : ℕ :=
  (movingPairFrequencyBase T).natAbs ^ (n + 1)

theorem movingPairFrequencyBase_dvd {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (b : Bool) :
    (T b).frequencyProduct ∣ movingPairFrequencyBase T := by
  cases b
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

theorem movingPairFrequencyModulus_precision {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) :
    movingPairFrequencyBase T ^ (n + 1) ∣ (movingPairFrequencyModulus T : ℤ) := by
  apply Int.dvd_natCast.mpr
  simp only [Int.natAbs_pow, movingPairFrequencyModulus]
  exact dvd_rfl

theorem movingPairFrequencyModulus_pos {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) :
    0 < movingPairFrequencyModulus T := by
  apply pow_pos
  exact Int.natAbs_pos.mpr (mul_ne_zero
    ((T false).frequencyProduct_ne_zero (hf false))
    ((T true).frequencyProduct_ne_zero (hf true)))

theorem movingPairFrequencyModulus_bound {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (B : ℕ)
    (hf : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B)) :
    movingPairFrequencyModulus T ≤ B ^ (2 * (2 ^ (n + 1) - 1) * (n + 1)) := by
  have h := Nat.mul_le_mul ((T false).frequencyProduct_bound B (hf false))
    ((T true).frequencyProduct_bound B (hf true))
  have hp := Nat.pow_le_pow_left h (n + 1)
  simpa only [movingPairFrequencyModulus, movingPairFrequencyBase, Int.natAbs_mul,
    ← pow_add, ← pow_mul, ← two_mul] using hp

theorem movingPairFrequencyModulus_exp {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (B : ℕ) (A m : ℝ)
    (hf : ∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B))
    (hB : (B : ℝ) ≤ Real.exp (A * m)) :
    (movingPairFrequencyModulus T : ℝ) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1) * (n + 1) : ℕ) * (A * m)) := by
  calc
    _ ≤ (B : ℝ) ^ (2 * (2 ^ (n + 1) - 1) * (n + 1)) := by
      exact_mod_cast movingPairFrequencyModulus_bound T B hf
    _ ≤ Real.exp (A * m) ^ (2 * (2 ^ (n + 1) - 1) * (n + 1)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- The hypotheses on the original frequency list supply all frequency
period and nonzero-modulus requirements of the prime comparison. -/
theorem movingPattern_frequency_modulus {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0) :
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    0 < movingPairFrequencyModulus T ∧
      (∀ b, (T b).frequencyProduct ∣ movingPairFrequencyBase T) ∧
      movingPairFrequencyBase T ^ (n + 1) ∣ (movingPairFrequencyModulus T : ℤ) := by
  dsimp only
  exact ⟨movingPairFrequencyModulus_pos _
    (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hf),
    movingPairFrequencyBase_dvd _, movingPairFrequencyModulus_precision _⟩

end Ostmann

end OAI
