import Mathlib.Data.List.NodupEquivFin
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.SmallReusePermutation

namespace OAI

namespace Balanced.Local.EqualityPattern

open Finset

def classSet {b κ : ℕ} (P : EqualityPattern b κ) (i : Fin b) :
    Finset (Fin (4 * b - κ)) := Finset.univ.image (P.classOf i)

@[simp]
theorem card_classSet {b κ : ℕ} (P : EqualityPattern b κ) (i : Fin b) :
    (P.classSet i).card = 4 := by
  rw [classSet, Finset.card_image_of_injective _ (P.withinTuple i)]
  simp

theorem biUnion_classSet {b κ : ℕ} (P : EqualityPattern b κ) :
    Finset.univ.biUnion P.classSet = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro a
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass a
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij⟩

@[simp]
theorem card_biUnion_classSet {b κ : ℕ} (P : EqualityPattern b κ) :
    (Finset.univ.biUnion P.classSet).card = 4 * b - κ := by
  rw [P.biUnion_classSet]
  simp

@[simp]
theorem sum_card_classSet {b κ : ℕ} (P : EqualityPattern b κ) :
    (∑ i : Fin b, (P.classSet i).card) = 4 * b := by
  simp [Nat.mul_comm]

theorem classSet_reuse_le {b κ : ℕ} (P : EqualityPattern b κ) :
    (∑ i : Fin b, (P.classSet i).card) -
      (Finset.univ.biUnion P.classSet).card ≤ κ := by
  rw [P.sum_card_classSet, P.card_biUnion_classSet]
  omega

theorem classSet_reuse_eq {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    (∑ i : Fin b, (P.classSet i).card) -
      (Finset.univ.biUnion P.classSet).card = κ := by
  rw [P.sum_card_classSet, P.card_biUnion_classSet]
  omega

theorem exists_smallReuseOrder {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2) :
    ∃ l : List (Fin b), l.Nodup ∧ l.toFinset = Finset.univ ∧
      Balanced.SmallReuseOrder P.classSet l := by
  apply Balanced.exists_smallReuseOrder P.classSet Finset.univ
  · intro i _ j _ hij
    exact P.pairOverlap i j hij
  · exact P.classSet_reuse_le.trans hκ

theorem exists_processing_perm {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2) :
    ∃ π : Equiv.Perm (Fin b), ∀ i : Fin b,
      (P.classSet (π i) ∩ (Finset.univ.filter (fun j : Fin b => j < i)).biUnion
        (fun j => P.classSet (π j))).card ≤ 1 := by
  obtain ⟨l, hnd, hfull, horder⟩ := P.exists_smallReuseOrder hκ
  exact Balanced.exists_perm_of_list_tail_overlap P.classSet l hnd hfull
    horder.tail_overlap

theorem generatorSet_prescribedTuple {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (i : Fin b) :
    generatorSet (prescribedTuple P a bits i) = (P.classSet i).image a.2 := by
  simp [generatorSet, prescribedTuple, classSet, Finset.image_image, Function.comp_def]

theorem prescribed_generator_overlap_card {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (hinj : Function.Injective a.2) (bits : Bits b) (i : Fin b) (s : Finset (Fin b)) :
    ((generatorSet (prescribedTuple P a bits i)) ∩
      s.biUnion (fun j => generatorSet (prescribedTuple P a bits j))).card =
      (P.classSet i ∩ s.biUnion P.classSet).card := by
  simp_rw [P.generatorSet_prescribedTuple]
  rw [← Finset.biUnion_image, ← Finset.image_inter _ _ hinj,
    Finset.card_image_of_injective _ hinj]

theorem exists_uniform_direction_order {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) :
    ∃ l : List (Fin b), l.Nodup ∧ l.toFinset = Finset.univ ∧
      ∀ (F : Type*) [DecidableEq F] (a : DirectionAssignment F b κ),
        Eligible P a → ∀ bits : Bits b,
          Balanced.SmallReuseOrder (fun i => generatorSet (prescribedTuple P a bits i)) l := by
  obtain ⟨l, hnd, hfull, horder⟩ := P.exists_smallReuseOrder hκ
  refine ⟨l, hnd, hfull, fun F _ a ha bits => ?_⟩
  simpa only [P.generatorSet_prescribedTuple] using horder.image a.2 ha.2.1

theorem exists_direction_processing_perm {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) :
    ∃ π : Equiv.Perm (Fin b), ∀ (F : Type*) [DecidableEq F]
      (a : DirectionAssignment F b κ), Eligible P a → ∀ (bits : Bits b) (i : Fin b),
      (generatorSet (prescribedTuple P a bits (π i)) ∩
        (Finset.univ.filter (fun j : Fin b => j < i)).biUnion
          (fun j => generatorSet (prescribedTuple P a bits (π j)))).card ≤ 1 := by
  obtain ⟨π, hπ⟩ := P.exists_processing_perm hκ
  refine ⟨π, fun F _ a ha bits i => ?_⟩
  have hclass := hπ i
  have h := P.prescribed_generator_overlap_card a ha.2.1 bits (π i)
    ((Finset.univ.filter (fun j : Fin b => j < i)).image π)
  simp only [Finset.image_biUnion] at h
  rw [h]
  exact hclass

end Balanced.Local.EqualityPattern

end OAI
