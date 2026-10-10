import OAI.Combinatorics.Ryser.Construction.GadgetDefinitions
import OAI.Combinatorics.Ryser.LineCover.DeletionDefinitions
import OAI.Combinatorics.Ryser.LineCover.Definitions

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable (k : Type*) [Field k] [Fintype k] [DecidableEq k]

def cubicShapes : Finset (Finset (Point k)) :=
  Finset.univ.image fun dz : NonzeroSlope k × k => cubicShape dz.1.val dz.2

theorem cubicShapes_card_le_square : (cubicShapes k).card ≤ Fintype.card k ^ 2 := by
  calc
    (cubicShapes k).card ≤
        (Finset.univ : Finset (NonzeroSlope k × k)).card :=
      Finset.card_image_le
    _ = Fintype.card (NonzeroSlope k) * Fintype.card k := by
      rw [Finset.card_univ, Fintype.card_prod]
    _ ≤ Fintype.card k * Fintype.card k :=
      Nat.mul_le_mul_right _
        (Fintype.card_subtype_le (fun d : k => d ≠ 0))
    _ = Fintype.card k ^ 2 := (pow_two _).symm

theorem cubicShapes_card_le : (cubicShapes k).card ≤ 3 * Fintype.card k ^ 3 := by
  have hq : 1 ≤ Fintype.card k := Nat.succ_le_of_lt Fintype.card_pos
  have hstep : Fintype.card k ^ 2 ≤ Fintype.card k ^ 3 := by
    rw [pow_succ (Fintype.card k) 2]
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left (Fintype.card k ^ 2) hq)
  exact (cubicShapes_card_le_square k).trans (hstep.trans (by omega))

variable {k}

@[simp] theorem mem_cubicShapes {S : Finset (Point k)} :
    S ∈ cubicShapes k ↔ ∃ d : NonzeroSlope k, ∃ z : k, cubicShape d.val z = S := by
  simp only [cubicShapes, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]

theorem cubicShape_mem_cubicShapes (d : NonzeroSlope k) (z : k) :
    cubicShape d.val z ∈ cubicShapes k :=
  Finset.mem_image.mpr ⟨(d, z), Finset.mem_univ _, rfl⟩

theorem cubicShapes_member_card {S : Finset (Point k)} (hS : S ∈ cubicShapes k) :
    S.card = Fintype.card k := by
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_card d.val z d.property

theorem cubicShapes_member_card_le {S : Finset (Point k)} (hS : S ∈ cubicShapes k) :
    S.card ≤ 3 * Fintype.card k := by
  rw [cubicShapes_member_card hS]
  omega

variable (k) in
theorem cubicShapes_sparse : LineCover.SparseShapes (cubicShapes k) 3 := by
  intro S hS ell _
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_inter_linePoints_card_le d.val z d.property ell

theorem cubicShapes_member_ne_linePoints (hcard : 3 < Fintype.card k)
    {S : Finset (Point k)} (hS : S ∈ cubicShapes k) (ell : AffineLine k) :
    S ≠ linePoints ell := by
  obtain ⟨d, z, rfl⟩ := mem_cubicShapes.mp hS
  exact cubicShape_ne_linePoints d.val z d.property hcard ell

def cubicTrialOutcome (d : NonzeroSlope k) (z : k) :
    LineCover.Outcome (cubicShapes k) 3 :=
  ⟨{⟨cubicShape d.val z, cubicShape_mem_cubicShapes d z⟩}, by simp⟩

@[simp] theorem cubicTrialOutcome_val (d : NonzeroSlope k) (z : k) :
    (cubicTrialOutcome d z).val =
      {⟨cubicShape d.val z, cubicShape_mem_cubicShapes d z⟩} := rfl

@[simp] theorem mem_deleted_cubicTrialOutcome (ignore : Finset (Finset (Point k)))
    (d : NonzeroSlope k) (z : k) (x : Point k) :
    x ∈ LineCover.deleted ignore (cubicTrialOutcome d z) ↔
      cubicShape d.val z ∉ ignore ∧ x ∈ cubicShape d.val z := by
  simp [LineCover.mem_deleted, cubicTrialOutcome]

@[simp] theorem deleted_empty_cubicTrialOutcome (d : NonzeroSlope k) (z : k) :
    LineCover.deleted ∅ (cubicTrialOutcome d z) = cubicShape d.val z := by
  ext x
  simp only [mem_deleted_cubicTrialOutcome, Finset.notMem_empty, not_false_eq_true, true_and]

@[simp] theorem mem_deleted_empty_cubicTrialOutcome
    (d : NonzeroSlope k) (z : k) (x : Point k) :
    x ∈ LineCover.deleted ∅ (cubicTrialOutcome d z) ↔ x ∈ cubicShape d.val z := by
  rw [deleted_empty_cubicTrialOutcome]

theorem cubicTrialOutcome_no_line (d : NonzeroSlope k) (z : k)
    (hcard : 3 < Fintype.card k) (ell : AffineLine k) :
    ¬ ∃ S ∈ (cubicTrialOutcome d z).val, S.val = linePoints ell := by
  rintro ⟨S, _, hline⟩
  exact cubicShapes_member_ne_linePoints hcard S.property ell hline

theorem selected_cubicShapes_ne_linePoints {n : ℕ}
    (ω : Fin n → LineCover.Outcome (cubicShapes k) 3)
    (hcard : 3 < Fintype.card k) {S : Finset (Point k)}
    (hS : S ∈ LineCover.selected ω) (ell : AffineLine k) : S ≠ linePoints ell := by
  obtain ⟨i, T, _, rfl⟩ := LineCover.mem_selected.mp hS
  exact cubicShapes_member_ne_linePoints hcard T.property ell

@[simp] theorem mem_selected_cubicTrials {n : ℕ}
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) (S : Finset (Point k)) :
    S ∈ LineCover.selected (fun i => cubicTrialOutcome (d i) (z i)) ↔
      ∃ i, cubicShape (d i).val (z i) = S := by
  simp [LineCover.mem_selected, cubicTrialOutcome]

@[simp] theorem mem_survivors_cubicTrials {n : ℕ}
    (ignore : Finset (Finset (Point k)))
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) (x : Point k) :
    x ∈ LineCover.survivors ignore (fun i => cubicTrialOutcome (d i) (z i)) ↔
      ∀ i, cubicShape (d i).val (z i) ∉ ignore → x ∉ cubicShape (d i).val (z i) := by
  simp only [LineCover.mem_survivors, mem_deleted_cubicTrialOutcome, not_and]

theorem survivors_cubicTrials_eq {n : ℕ}
    (d : Fin n → NonzeroSlope k) (z : Fin n → k) :
    LineCover.survivors ∅ (fun i => cubicTrialOutcome (d i) (z i)) =
      Finset.univ \ Finset.univ.biUnion (fun i => cubicShape (d i).val (z i)) := by
  simp only [LineCover.survivors, deleted_empty_cubicTrialOutcome]

end RyserCoveringCounterexample.Construction

end

end OAI
