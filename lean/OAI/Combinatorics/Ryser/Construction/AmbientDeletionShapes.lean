import OAI.Combinatorics.Ryser.Construction.CoverPencil
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import OAI.Combinatorics.Ryser.LineCover.Process
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def ambientShapes (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Finset (Point F)) := Finset.univ.image linePoints

theorem linePoints_mem_ambientShapes (l : AffineLine F) :
    linePoints l ∈ ambientShapes F := Finset.mem_image_of_mem _ (Finset.mem_univ l)

theorem ambient_linePoints_injective : Function.Injective (linePoints (F := F)) := by
  intro l m h
  by_contra hlm
  have hbound := card_linePoints_inter_le_one hlm
  rw [h, Finset.inter_self, card_linePoints] at hbound
  exact (Fintype.one_lt_card : 1 < Fintype.card F).not_ge hbound

theorem ambientShapes_count_le {D : ℕ} (hD : 2 ≤ D) :
    (ambientShapes F).card ≤ D * Fintype.card F ^ D := by
  have hq : 1 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.card_pos
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ D :=
    pow_le_pow_right₀ hq hD
  calc
    (ambientShapes F).card ≤ Fintype.card (AffineLine F) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = Fintype.card F * (Fintype.card F + 1) := card_affineLine
    _ ≤ 2 * Fintype.card F ^ 2 := by nlinarith
    _ ≤ D * Fintype.card F ^ D := Nat.mul_le_mul hD hpow

theorem ambientShapes_size_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset (Point F)) (hS : S ∈ ambientShapes F) :
    S.card ≤ D * Fintype.card F := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hS
  rw [card_linePoints]
  simpa only [one_mul] using Nat.mul_le_mul_right (Fintype.card F) hD

theorem ambientShapes_sparse {D : ℕ} (hD : 1 ≤ D) :
    LineCover.SparseShapes (ambientShapes F) D := by
  intro S hS l hne
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hS
  have hml : m ≠ l := fun h => hne (congrArg linePoints h)
  exact (card_linePoints_inter_le_one hml).trans hD

def ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F)) (hB : B.card ≤ D) :
    LineCover.Outcome (ambientShapes F) D :=
  ⟨B.image (fun l => (⟨linePoints l, linePoints_mem_ambientShapes l⟩ :
      ↥(ambientShapes F))), Finset.card_image_le.trans hB⟩

theorem mem_deleted_ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) (ignore : Finset (Finset (Point F))) (x : Point F) :
    x ∈ LineCover.deleted ignore (ambientLineOutcome B hB) ↔
      ∃ l ∈ B, linePoints l ∉ ignore ∧ Incidence x l := by
  rw [LineCover.mem_deleted]
  constructor
  · rintro ⟨S, hS, hignore, hx⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨l, hl, hignore, (mem_linePoints x l).mp hx⟩
  · rintro ⟨l, hl, hignore, hx⟩
    exact ⟨⟨linePoints l, linePoints_mem_ambientShapes l⟩,
      Finset.mem_image_of_mem _ hl, hignore, (mem_linePoints x l).mpr hx⟩

theorem ambientLineOutcome_lists_line {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) (l : AffineLine F) :
    (∃ S ∈ (ambientLineOutcome B hB).val, S.val = linePoints l) ↔ l ∈ B := by
  constructor
  · rintro ⟨S, hS, heq⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    exact ambient_linePoints_injective heq ▸ hm
  · intro hl
    exact ⟨⟨linePoints l, linePoints_mem_ambientShapes l⟩,
      Finset.mem_image_of_mem _ hl, rfl⟩

theorem deleted_empty_ambientLineOutcome {D : ℕ} (B : Finset (AffineLine F))
    (hB : B.card ≤ D) :
    LineCover.deleted ∅ (ambientLineOutcome B hB) = B.biUnion linePoints := by
  ext x
  simp only [mem_deleted_ambientLineOutcome, Finset.notMem_empty, not_false_eq_true, true_and,
    Finset.mem_biUnion, mem_linePoints]

def ambientDeletionConstant (s K : ℕ) : ℕ :=
  2 + (s - 1) ^ 2 + 2 * K + 2 * K * (s - 1)

theorem ambientDeletionConstant_two_le (s K : ℕ) :
    2 ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_lines_le (s K : ℕ) :
    (s - 1) ^ 2 ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_trials_le (s K : ℕ) :
    2 * K ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

theorem ambientDeletionConstant_lineRate_le (s K : ℕ) :
    2 * K * (s - 1) ≤ ambientDeletionConstant s K := by
  unfold ambientDeletionConstant
  omega

end RyserCoveringCounterexample.Construction

end

end OAI
