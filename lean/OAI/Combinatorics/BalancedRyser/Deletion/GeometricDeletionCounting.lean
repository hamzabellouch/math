import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace GeometricDeletionCounting

variable {F : Type*} [Fintype F] [DecidableEq F]

def offsetsAt (D : Finset (Line F)) (d : Direction F) : Finset F :=
  Finset.univ.filter (fun a => (d, a) ∈ D)

@[simp] theorem mem_offsetsAt (D : Finset (Line F)) (d : Direction F) (a : F) :
    a ∈ offsetsAt D d ↔ (d, a) ∈ D := by
  simp [offsetsAt]

def assemble (S : Direction F → Finset F) : Finset (Line F) :=
  Finset.univ.biUnion (fun d => (S d).image (fun a => (d, a)))

@[simp] theorem mem_assemble (S : Direction F → Finset F) (d : Direction F) (a : F) :
    (d, a) ∈ assemble S ↔ a ∈ S d := by
  simp [assemble]

@[simp] theorem offsetsAt_assemble (S : Direction F → Finset F) (d : Direction F) :
    offsetsAt (assemble S) d = S d := by
  ext a
  simp

@[simp] theorem assemble_offsetsAt (D : Finset (Line F)) :
    assemble (offsetsAt D) = D := by
  ext l
  obtain ⟨d, a⟩ := l
  simp

theorem card_offsetsAt (D : Finset (Line F)) (d : Direction F) :
    (offsetsAt D d).card = (D.filter (fun l => l.1 = d)).card := by
  apply Finset.card_bij (fun a _ => (d, a))
  · intro a ha
    simpa using ha
  · intro a _ b _ hab
    exact (Prod.mk.inj hab).2
  · intro l hl
    obtain ⟨hlD, hld⟩ := Finset.mem_filter.mp hl
    refine ⟨l.2, ?_, ?_⟩
    · have heq : (d, l.2) = l := Prod.ext hld.symm rfl
      simpa only [mem_offsetsAt, heq] using hlD
    · exact Prod.ext hld.symm rfl

variable [Field F]

def deletionEquivFamilies (k : ℕ) :
    DeletionSet F k ≃ (Direction F → {S : Finset F // S.card = k}) where
  toFun D d := ⟨offsetsAt D.val d, by rw [card_offsetsAt]; exact D.property d⟩
  invFun S := ⟨assemble (fun d => (S d).val), by
    intro d
    rw [← card_offsetsAt, offsetsAt_assemble]
    exact (S d).property⟩
  left_inv D := by
    apply Subtype.ext
    exact assemble_offsetsAt D.val
  right_inv S := by
    funext d
    apply Subtype.ext
    exact offsetsAt_assemble (fun d => (S d).val) d

theorem card_deletionSet (k : ℕ) :
    Fintype.card (DeletionSet F k) =
      (Nat.choose (Fintype.card F) k) ^ (Fintype.card F + 1) := by
  rw [Fintype.card_congr (deletionEquivFamilies (F := F) k)]
  simp [Direction]

theorem nonempty_deletionSet {k : ℕ} (hk : k ≤ Fintype.card F) :
    Nonempty (DeletionSet F k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_deletionSet]
  exact pow_pos (Nat.choose_pos hk) _

theorem nonempty_deletionSet_iff (k : ℕ) :
    Nonempty (DeletionSet F k) ↔ k ≤ Fintype.card F := by
  constructor
  · intro h
    have hc : 0 < Fintype.card (DeletionSet F k) := Fintype.card_pos_iff.mpr h
    rw [card_deletionSet] at hc
    by_contra hn
    have hzero : Nat.choose (Fintype.card F) k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hzero] at hc
  · exact nonempty_deletionSet

theorem uniformDeletionMass_eq (k : ℕ) :
    uniformDeletionMass (F := F) k =
      ((Nat.choose (Fintype.card F) k : ℝ) ^ (Fintype.card F + 1))⁻¹ := by
  simp [uniformDeletionMass, card_deletionSet]

theorem card_deleted_lines {k : ℕ} (D : DeletionSet F k) :
    D.val.card = k * (Fintype.card F + 1) := by
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := D.val) (t := (Finset.univ : Finset (Direction F)))
    (f := fun l : Line F => l.1) (fun _ _ => Finset.mem_univ _)
  have hp : ∀ d, (D.val.filter (fun l => l.1 = d)).card = k := D.property
  calc
    D.val.card = ∑ d : Direction F, (D.val.filter (fun l => l.1 = d)).card := hcard
    _ = ∑ _d : Direction F, k := Finset.sum_congr rfl (fun d _ => hp d)
    _ = k * (Fintype.card F + 1) := by simp [Direction, Nat.mul_comm]

end GeometricDeletionCounting
end Balanced

end OAI
