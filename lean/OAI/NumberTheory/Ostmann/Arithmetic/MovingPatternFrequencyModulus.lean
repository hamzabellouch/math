import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelModulus
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData

namespace OAI

/-! # The actual pattern denominator satisfies the frequency-model requirements -/

namespace Ostmann
open scoped Classical

theorem movingPattern_frequencyProduct_dvd {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (S : Finset ℤ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (b : Bool) :
    (movingPatternFinBulkData e n m
      (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection S n side t))
      small slot perm pattern b).frequencyProduct ∣ (frequencyModelBase S n t : ℤ) := by
  apply Int.natAbs_dvd.mp
  apply Int.natCast_dvd_natCast.mpr
  rw [movingPatternFinBulkData_build, buildMovingSlotData_frequencyProduct_abs]
  cases b
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

theorem prime_coprime_frequencyModelBase (S : Finset ℤ) (N p n : ℕ)
    (hp : p.Prime) (hpN : N < p) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (t : FrequencyTree (S × S) n) : p.Coprime (frequencyModelBase S n t) := by
  have h (b : Bool) : p.Coprime (historyFrequencyProduct S n (frequencyPairProjection S n b t)) := by
    have hb := prime_coprime_historyFrequencyModulus S N p hp hpN hS n 0
      (frequencyPairProjection S n b t)
    exact Nat.Coprime.of_dvd_right (dvd_pow_self _ (by decide : (0 + 2 : ℕ) ≠ 0)) hb
  exact (h false).mul_right (h true)

theorem frequencyModelModulus_bound (S : Finset ℤ) (N n : ℕ)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) (t : FrequencyTree (S × S) n) :
    frequencyModelBase S n t ^ (n - 1 + 2) ≤
      N ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) := by
  exact (Nat.pow_le_pow_left (frequencyModelBase_le S n N t hN) _).trans_eq (pow_mul _ _ _).symm

end Ostmann

end OAI
