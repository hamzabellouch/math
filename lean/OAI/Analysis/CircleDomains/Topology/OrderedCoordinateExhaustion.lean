import OAI.Analysis.CircleDomains.Selection.CountableMarks
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Finite coordinate lists keep their given order. A prescribed real
subfamily is retained through an explicit injection into every sufficiently
large list, even when the full countable order has type greater than omega. -/

open Set Function Filter
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_ordered_coordinate_exhaustion
    {C : Type*} [LinearOrder C] [Countable C] (real : ℕ → C) (hinj : Injective real) :
    ∃ (size : ℕ → ℕ) (label : ∀ n, Fin (size n) ↪o C)
      (slot : ∀ n, Fin (n + 1) → Fin (size n)),
      (∀ n, 0 < size n) ∧
      (∀ n, Injective (slot n)) ∧
      (∀ n j, label n (slot n j) = real j) ∧
      Monotone (fun n => range (label n)) ∧
      ∀ c, ∀ᶠ n in atTop, c ∈ range (label n) := by
  classical
  obtain ⟨F, hF, hmono, hcover⟩ := exists_increasing_finite_marks C
  let L (n : ℕ) : Finset C := (hF n).toFinset ∪ (Finset.range (n + 1)).image real
  let label (n : ℕ) : Fin (L n).card ↪o C := (L n).orderEmbOfFin rfl
  have hmem (n : ℕ) (j : Fin (n + 1)) : real j ∈ L n := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr j.isLt, rfl⟩)
  let slot (n : ℕ) (j : Fin (n + 1)) : Fin (L n).card :=
    ((L n).orderIsoOfFin rfl).symm ⟨real j, hmem n j⟩
  have hslot (n : ℕ) (j : Fin (n + 1)) : label n (slot n j) = real j :=
    congrArg Subtype.val (((L n).orderIsoOfFin rfl).apply_symm_apply ⟨real j, hmem n j⟩)
  have hrange (n : ℕ) : range (label n) = (L n : Set C) := (L n).range_orderEmbOfFin rfl
  refine ⟨fun n => (L n).card, label, slot, ?_, ?_, hslot, ?_, ?_⟩
  · intro n
    exact Finset.card_pos.mpr ⟨real 0, hmem n ⟨0, Nat.succ_pos n⟩⟩
  · intro n i j hij
    apply Fin.ext
    apply hinj
    exact (hslot n i).symm.trans ((congrArg (label n) hij).trans (hslot n j))
  · intro n m hnm
    change range (label n) ⊆ range (label m)
    rw [hrange, hrange]
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union_left _ ((hF m).mem_toFinset.mpr
        (hmono hnm ((hF n).mem_toFinset.mp hc)))
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.add_le_add_right hnm 1)), rfl⟩)
  · intro c
    filter_upwards [hcover c] with n hn
    rw [hrange]
    exact Finset.mem_union_left _ ((hF n).mem_toFinset.mpr hn)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
