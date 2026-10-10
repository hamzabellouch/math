import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.BalancedRyser.Probability.TupleExposure

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

section FiniteLabels
variable {α : Type*} [Fintype α] [DecidableEq α]

def restrictedGeneratorLabels (old : Finset α) (mask : Finset (Fin 4)) :
    Finset (Fin 4 → α) :=
  Fintype.piFinset (fun i => if i ∈ mask then old else Finset.univ)

omit [DecidableEq α] in
theorem card_restrictedGeneratorLabels (old : Finset α) (mask : Finset (Fin 4)) :
    (restrictedGeneratorLabels old mask).card =
      old.card ^ mask.card * Fintype.card α ^ (4 - mask.card) := by
  rw [restrictedGeneratorLabels, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_univ]
  rw [Finset.prod_ite]
  have hcomp : ((Finset.univ : Finset (Fin 4)) \ mask).card = 4 - mask.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  simp [← Finset.sdiff_eq_filter, hcomp]

def generatorLabelsWithOldCount (old : Finset α) (j : ℕ) : Finset (Fin 4 → α) :=
  Finset.univ.filter (fun g => (Finset.univ.filter (fun i => g i ∈ old)).card = j)

theorem generatorLabelsWithOldCount_subset (old : Finset α) (j : ℕ) :
    generatorLabelsWithOldCount old j ⊆
      (Finset.univ.powersetCard j).biUnion (restrictedGeneratorLabels old) := by
  intro g hg
  let mask : Finset (Fin 4) := Finset.univ.filter (fun i => g i ∈ old)
  have hmask : mask.card = j := (Finset.mem_filter.mp hg).2
  refine Finset.mem_biUnion.mpr ⟨mask,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hmask⟩, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : i ∈ mask
  · simpa only [ite_eq_left hi] using (Finset.mem_filter.mp hi).2
  · simp [hi]

theorem card_generatorLabelsWithOldCount_le (old : Finset α) (j : ℕ) :
    (generatorLabelsWithOldCount old j).card ≤
      Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j) := by
  calc
    (generatorLabelsWithOldCount old j).card ≤
        ((Finset.univ.powersetCard j).biUnion (restrictedGeneratorLabels old)).card :=
      Finset.card_le_card (generatorLabelsWithOldCount_subset old j)
    _ ≤ ∑ mask ∈ Finset.univ.powersetCard j, (restrictedGeneratorLabels old mask).card :=
      Finset.card_biUnion_le
    _ = ∑ _mask ∈ (Finset.univ : Finset (Fin 4)).powersetCard j,
        old.card ^ j * Fintype.card α ^ (4 - j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      rw [card_restrictedGeneratorLabels, (Finset.mem_powersetCard.mp hmask).2]
    _ = Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j) := by
      simp [Nat.mul_assoc]

def tupleCodesWithOldCount (old : Finset α) (j : ℕ) :
    Finset ((Fin 4 → α) × (Fin 4 → Bool)) :=
  (generatorLabelsWithOldCount old j).product Finset.univ

theorem card_tupleCodesWithOldCount_le (old : Finset α) (j : ℕ) :
    (tupleCodesWithOldCount old j).card ≤
      16 * (Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j)) := by
  rw [tupleCodesWithOldCount, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ]
  have hbits : Fintype.card (Fin 4 → Bool) = 16 := by decide
  rw [hbits, Nat.mul_comm]
  exact Nat.mul_le_mul_left 16 (card_generatorLabelsWithOldCount_le old j)

omit [Fintype α] in

theorem exposed_generators_card_le_twenty_four {ι : Type*} [DecidableEq ι]
    (A : ι → Finset α) (s : Finset ι) (hs : s.card ≤ 6)
    (hfour : ∀ i ∈ s, (A i).card ≤ 4) : (s.biUnion A).card ≤ 24 := by
  calc
    (s.biUnion A).card ≤ ∑ i ∈ s, (A i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, 4 := Finset.sum_le_sum hfour
    _ ≤ 24 := by simp; omega

theorem card_tupleCodesWithOldCount_le_uniform (old : Finset α) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (256 * 24 ^ 4) * Fintype.card α ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by
    interval_cases j <;> decide
  have hpow : old.card ^ j ≤ 24 ^ 4 := by
    calc
      old.card ^ j ≤ 24 ^ j := Nat.pow_le_pow_left hold j
      _ ≤ 24 ^ 4 := Nat.pow_le_pow_right (by omega) hj
  calc
    (tupleCodesWithOldCount old j).card ≤
        16 * (Nat.choose 4 j * old.card ^ j * Fintype.card α ^ (4 - j)) :=
      card_tupleCodesWithOldCount_le old j
    _ ≤ 16 * (16 * 24 ^ 4 * Fintype.card α ^ (4 - j)) := by gcongr
    _ = (256 * 24 ^ 4) * Fintype.card α ^ (4 - j) := by ring

end FiniteLabels

theorem card_tupleCodesWithOldCount_le_field {F : Type*} [Fintype F]
    [Nonempty F] [DecidableEq F] (old : Finset (Direction F)) (j : ℕ)
    (hold : old.card ≤ 24) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (4096 * 24 ^ 4) * Fintype.card F ^ (4 - j) := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    calc
      2 ^ (4 - j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 16 := rfl
  calc
    (tupleCodesWithOldCount old j).card ≤
        (256 * 24 ^ 4) * Fintype.card (Direction F) ^ (4 - j) :=
      card_tupleCodesWithOldCount_le_uniform old j hold hj
    _ ≤ (256 * 24 ^ 4) * (2 * Fintype.card F) ^ (4 - j) := by gcongr
    _ = (256 * 24 ^ 4) * (2 ^ (4 - j) * Fintype.card F ^ (4 - j)) := by rw [Nat.mul_pow]
    _ ≤ (256 * 24 ^ 4) * (16 * Fintype.card F ^ (4 - j)) := by gcongr
    _ = (4096 * 24 ^ 4) * Fintype.card F ^ (4 - j) := by ring

end Balanced

end OAI
