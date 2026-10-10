import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelPairSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyModulus

namespace OAI

/-! # A modulus using only the frequencies of the two fixed histories -/

namespace Ostmann
open scoped Classical

def frequencyModelBase (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n) : ℕ :=
  historyFrequencyProduct S n (frequencyPairProjection S n false t) *
    historyFrequencyProduct S n (frequencyPairProjection S n true t)

theorem frequencyModelBase_pos (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) : 0 < frequencyModelBase S n t :=
  Nat.mul_pos (historyFrequencyProduct_pos S hS n _) (historyFrequencyProduct_pos S hS n _)

theorem frequencyModelBase_roots (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (b : Bool) (j : Fin (2 ^ n - 1)) :
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣
      frequencyModelBase S n t := by
  have hj : j.val < (singleFrequencySplitList S n (frequencyPairProjection S n b t)).length := by
    simpa only [singleFrequencySplitList_length] using j.isLt
  have hmem : singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val ∈
      singleFrequencySplitList S n (frequencyPairProjection S n b t) := by
    rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hd := history_node_dvd_frequencyProduct S n (frequencyPairProjection S n b t) _ hmem
  cases b
  · exact dvd_mul_of_dvd_left hd _
  · exact dvd_mul_of_dvd_right hd _

theorem frequencyModelBase_le (S : Finset ℤ) (n N : ℕ) (t : FrequencyTree (S × S) n)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) :
    frequencyModelBase S n t ≤ N ^ (2 * (2 ^ (n + 1) - 1)) := by
  calc
    _ ≤ N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
      Nat.mul_le_mul (historyFrequencyProduct_le S N hN n _) (historyFrequencyProduct_le S N hN n _)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem buildMovingSlotData_frequencyProduct_abs {σ : Type*}
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a).frequencyProduct.natAbs =
      historyFrequencyProduct S n t := by
  induction a with
  | leaf => rfl
  | @node n u l r ihL ihR =>
    simp only [buildMovingSlotData, frequencyTreeMap, MovingSlotData.frequencyProduct,
      Int.natAbs_mul, historyFrequencyProduct, ihL, ihR]

theorem frequencyModelBase_actual {σ : Type*}
    (S : Finset ℤ) (n m : ℕ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List σ) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ) (a : Bool → MovingSampleSlots σ n) :
    (movingPairFrequencyBase (fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b))).natAbs = frequencyModelBase S n t := by
  simp only [movingPairFrequencyBase, Int.natAbs_mul, buildMovingSlotData_frequencyProduct_abs,
    frequencyModelBase]

theorem frequencyModelBase_actual_dvd {σ : Type*}
    (S : Finset ℤ) (n m : ℕ) (t : FrequencyTree (S × S) n)
    (small : Bool → TreeLeafTuple (List σ) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ) (a : Bool → MovingSampleSlots σ n) (b : Bool) :
    (buildMovingSlotData n (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)).frequencyProduct ∣ (frequencyModelBase S n t : ℤ) := by
  let T := fun b => buildMovingSlotData n
    (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
    (small b) (bulkSlotLeaves n m slot) (a b)
  have h := Int.natAbs_dvd_natAbs.mpr (movingPairFrequencyBase_dvd T b)
  rw [frequencyModelBase_actual S n m t small slot a] at h
  exact Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr h)

theorem frequencyModelModulus_precision (R n : ℕ) :
    (R : ℤ) ^ (n + 1) ∣ ((R ^ (n - 1 + 2) : ℕ) : ℤ) := by
  rw [Nat.cast_pow]
  exact pow_dvd_pow (R : ℤ) (by omega)

end Ostmann

end OAI
