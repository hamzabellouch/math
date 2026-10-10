import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Model
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

namespace OAI

/-!
# Equal-weight records and exact dictionary capacities

An additional prime can distinguish unequal weights, but cannot distinguish
different masks of equal weight. These deterministic bounds handle that case,
including the full-mask endpoint of the right-prefix refinement.
-/

namespace LowSpaceSubsetSum

variable {ι : Type*} [DecidableEq ι]

instance : DecidableEq (Entry ι) := fun a b =>
  if h : a.value = b.value ∧ a.mask = b.mask then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro hab; exact h (hab ▸ ⟨rfl, rfl⟩))

/-- Equal-weight records are uniquely identified by their top masks. -/
theorem same_weight_card_le_masks (U : Finset (Entry ι)) (x : ℤ) :
    (U.filter fun e => e.value = x).card ≤ (U.image Entry.mask).card := by
  classical
  have hinj : Set.InjOn Entry.mask (↑(U.filter fun e => e.value = x) : Set (Entry ι)) := by
    intro e he f hf hmask
    have heq := (Finset.mem_filter.mp he).2
    have hfq := (Finset.mem_filter.mp hf).2
    cases e
    cases f
    simp_all
  calc
    _ = ((U.filter fun e => e.value = x).image Entry.mask).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (U.image Entry.mask).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- Prescribed mask size bounds all equal-weight records by a binomial count. -/
theorem same_weight_card_le_choose (U : Finset (Entry ι)) (top : Finset ι)
    (k : ℕ) (hmask : ∀ e ∈ U, e.mask ⊆ top ∧ e.mask.card = k) (x : ℤ) :
    (U.filter fun e => e.value = x).card ≤ top.card.choose k := by
  apply (same_weight_card_le_masks U x).trans
  calc
    _ ≤ (top.powersetCard k).card := by
      apply Finset.card_le_card
      intro D hD
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hD
      exact Finset.mem_powersetCard.mpr (hmask e he)
    _ = _ := Finset.card_powersetCard _ _

/-- Fixing both the exact weight and the entire mask leaves at most one key. -/
theorem full_mask_same_weight_card_le_one (U : Finset (Entry ι))
    (x : ℤ) (D : Finset ι) :
    (U.filter fun e => e.value = x ∧ e.mask = D).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he0, he1⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨hf0, hf1⟩ := (Finset.mem_filter.mp hf).2
  cases e
  cases f
  simp_all

omit [DecidableEq ι] in
/-- The complete bucket fits when both its equal- and unequal-weight parts fit.
This counts keys, rather than raw tuples producing those keys. -/
theorem bucket_card_le_of_parts (U : Finset (Entry ι)) (x : ℤ) (C A B : ℕ)
    (hneq : (U.filter fun e => e.value ≠ x).card ≤ A)
    (heq : (U.filter fun e => e.value = x).card ≤ B) (hcap : A + B ≤ C) :
    U.card ≤ C := by
  have h := Finset.card_filter_add_card_filter_not (s := U) (p := fun e => e.value = x)
  have hcard : (U.filter fun e => e.value = x).card +
      (U.filter fun e => e.value ≠ x).card = U.card := by
    simpa only [ne_eq] using h
  omega

end LowSpaceSubsetSum

end OAI
