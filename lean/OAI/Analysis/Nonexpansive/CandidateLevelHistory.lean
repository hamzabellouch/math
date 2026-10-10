import OAI.Analysis.Nonexpansive.CandidateLevel
import OAI.Analysis.Nonexpansive.ParentReturnHistory
import OAI.Analysis.Nonexpansive.FinitePrefixEmbedding
import OAI.Analysis.Nonexpansive.ListRunPrefix

namespace OAI

/-!
# The literal chronological history of a completed candidate level

The parent sequences append their actual records to one shared history. The
concatenated group ordinal identifies both the stored record and exactly
the prefix used to choose its budget, compact prediction set and detector.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints.CandidateContext

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (hanchor : C.anchor = A.x) {τ : ℝ} (hτ : 0 < τ)

/-- The actual parent sequence at a natural stage of the level recursion. -/
def stageReturn (n : ℕ) :
    C.ParentReturn (C.parentAt n) (C.levelStates A hanchor hτ n) τ :=
  C.selectParent A hanchor (C.parentAt n) (C.levelStates A hanchor hτ n) hτ

def stageRecords (n : ℕ) : List (CandidateRecord C) :=
  (C.stageReturn A hanchor hτ n).records

/-- The number of candidates actually selected for each parent. -/
def groupN (p : Fin C.frontier.size) : ℕ := (C.group A hanchor hτ p).N

@[simp] theorem stageRecords_length (n : ℕ) :
    (C.stageRecords A hanchor hτ n).length = (C.stageReturn A hanchor hτ n).N :=
  (C.stageReturn A hanchor hτ n).records_length

/-- This is the append equation of the concrete selected sequence. -/
theorem levelStates_succ_entries (n : ℕ) :
    (C.levelStates A hanchor hτ (n + 1)).entries =
      (C.levelStates A hanchor hτ n).entries ++ C.stageRecords A hanchor hτ n :=
  (C.stageReturn A hanchor hτ n).finalState_entries

theorem levelStates_prefix {i j : ℕ} (h : i ≤ j) :
    (C.levelStates A hanchor hτ i).entries <+:
      (C.levelStates A hanchor hτ j).entries :=
  ListRunPrefix.prefix_of_le (fun n => (C.levelStates A hanchor hτ n).entries)
    (C.stageRecords A hanchor hτ) (C.levelStates_succ_entries A hanchor hτ) h

/-- The length counts every selected record, before discarding zero weights. -/
theorem levelStates_length (n : ℕ) :
    (C.levelStates A hanchor hτ n).entries.length =
      ∑ i : Fin n, (C.stageReturn A hanchor hτ i.val).N := by
  calc
    _ = ∑ i ∈ Finset.range n, (C.stageRecords A hanchor hτ i).length :=
      ListRunPrefix.length_eq_sum
        (fun n => (C.levelStates A hanchor hτ n).entries)
        (C.stageRecords A hanchor hτ) rfl
        (C.levelStates_succ_entries A hanchor hτ) n
    _ = ∑ i ∈ Finset.range n, (C.stageReturn A hanchor hτ i).N := by
      simp only [C.stageRecords_length]
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun i => (C.stageReturn A hanchor hτ i).N) n).symm

theorem levelStates_length_eq_prefix (n : ℕ) (hn : n ≤ C.frontier.size) :
    (C.levelStates A hanchor hτ n).entries.length =
      ∑ i : Fin n, C.groupN A hanchor hτ (FinitePrefix.inclusion hn i) := by
  rw [C.levelStates_length A hanchor hτ]
  all_goals rfl

/-- The state before a parent group has exactly the preceding groups' size. -/
theorem levelStates_length_eq_offset (p : Fin C.frontier.size) :
    (C.levelStates A hanchor hτ p.val).entries.length =
      OrderedGroupConcat.offset (C.groupN A hanchor hτ) p := by
  rw [C.levelStates_length_eq_prefix A hanchor hτ p.val p.isLt.le,
    FinitePrefix.sum_prefix_eq_sum_cutoff]
  simp only [OrderedGroupConcat.offset, Finset.sum_filter]
  all_goals rfl

/-- The final history consists of exactly all candidate groups. -/
theorem finalState_length_eq_total :
    (C.finalState A hanchor hτ).entries.length =
      OrderedGroupConcat.total (C.groupN A hanchor hτ) := by
  change (C.levelStates A hanchor hτ C.frontier.size).entries.length = _
  rw [C.levelStates_length A hanchor hτ]
  all_goals rfl

theorem group_finalState_eq (p : Fin C.frontier.size) :
    (C.group A hanchor hτ p).finalState =
      C.levelStates A hanchor hτ (p.val + 1) := rfl

theorem group_finalState_prefix (p : Fin C.frontier.size) :
    (C.group A hanchor hτ p).finalState.entries <+:
      (C.finalState A hanchor hτ).entries := by
  rw [C.group_finalState_eq A hanchor hτ p]
  exact C.levelStates_prefix A hanchor hτ (Nat.succ_le_of_lt p.isLt)

/-- The state before a local candidate has its actual global ordinal as length. -/
theorem group_state_length (p : Fin C.frontier.size)
    (i : Fin (C.group A hanchor hτ p).N) :
    ((C.group A hanchor hτ p).state i.castSucc).entries.length =
      OrderedGroupConcat.offset (C.groupN A hanchor hτ) p + i.val := by
  calc
    _ = (C.levelStates A hanchor hτ p.val).entries.length + i.val :=
      (C.group A hanchor hτ p).state_length i.val i.isLt.le
    _ = _ := by rw [C.levelStates_length_eq_offset A hanchor hτ p]

/-- Later groups do not alter the prefix used by this candidate. -/
theorem group_state_eq_final_take (p : Fin C.frontier.size)
    (i : Fin (C.group A hanchor hτ p).N) :
    ((C.group A hanchor hτ p).state i.castSucc).entries =
      (C.finalState A hanchor hτ).entries.take
        (OrderedGroupConcat.offset (C.groupN A hanchor hτ) p + i.val) := by
  have hp : ((C.group A hanchor hτ p).state i.castSucc).entries <+:
      (C.group A hanchor hτ p).finalState.entries := by
    change ((C.group A hanchor hτ p).state
      ⟨i.val, Nat.lt_succ_of_le i.isLt.le⟩).entries <+: _
    rw [(C.group A hanchor hτ p).state_entries_eq_final_take i.val i.isLt.le]
    exact List.take_prefix _ _
  have heq := List.prefix_iff_eq_take.mp
    (hp.trans (C.group_finalState_prefix A hanchor hτ p))
  simpa only [C.group_state_length A hanchor hτ p i] using heq

/-- The actual global entry at a group coordinate is its originally chosen record. -/
theorem finalState_get_groupRecord (p : Fin C.frontier.size)
    (i : Fin (C.group A hanchor hτ p).N) :
    (C.finalState A hanchor hτ).entries[
      OrderedGroupConcat.offset (C.groupN A hanchor hτ) p + i.val]'(by
        rw [C.finalState_length_eq_total A hanchor hτ]
        exact (OrderedGroupConcat.group (C.groupN A hanchor hτ) p i).isLt) =
      (C.group A hanchor hτ p).record i := by
  have hb : OrderedGroupConcat.offset (C.groupN A hanchor hτ) p + i.val <
      (C.group A hanchor hτ p).finalState.entries.length := by
    rw [(C.group A hanchor hτ p).finalState_length,
      C.levelStates_length_eq_offset A hanchor hτ p]
    exact Nat.add_lt_add_left i.isLt _
  have hget := (C.group A hanchor hτ p).finalState_get_record i
  simp only [C.levelStates_length_eq_offset A hanchor hτ p] at hget
  exact ((C.group_finalState_prefix A hanchor hτ p).getElem hb).symm.trans hget

/-- Decode the actual concatenated ordinal into its originally chosen record. -/
def levelRecord (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    CandidateRecord C :=
  let s := (OrderedGroupConcat.equiv (C.groupN A hanchor hτ)).symm i
  (C.group A hanchor hτ s.1).record s.2

@[simp] theorem levelRecord_group (p : Fin C.frontier.size)
    (i : Fin (C.group A hanchor hτ p).N) :
    C.levelRecord A hanchor hτ
      (OrderedGroupConcat.group (C.groupN A hanchor hτ) p i) =
      (C.group A hanchor hτ p).record i := by
  change (fun s : OrderedGroupConcat.Index (C.groupN A hanchor hτ) =>
    (C.group A hanchor hτ s.1).record s.2)
      ((OrderedGroupConcat.equiv (C.groupN A hanchor hτ)).symm
        (OrderedGroupConcat.equiv (C.groupN A hanchor hτ) ⟨p, i⟩)) = _
  rw [Equiv.symm_apply_apply]

theorem levelRecord_parent
    (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    (C.levelRecord A hanchor hτ i).parent =
      OrderedGroupConcat.parent (C.groupN A hanchor hτ) i := by
  obtain ⟨⟨p, j⟩, rfl⟩ :=
    (OrderedGroupConcat.equiv (C.groupN A hanchor hτ)).surjective i
  change (C.levelRecord A hanchor hτ
    (OrderedGroupConcat.group (C.groupN A hanchor hτ) p j)).parent = _
  exact (congrArg (fun r : CandidateRecord C => r.parent)
    (C.levelRecord_group A hanchor hτ p j)).trans
      (((C.group A hanchor hτ p).record_parent j).trans
        ((C.parentAt_fin p).trans
          (OrderedGroupConcat.parent_group (C.groupN A hanchor hτ) p j).symm))

theorem finalState_get_levelRecord
    (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    (C.finalState A hanchor hτ).entries[i.val]'(by
      rw [C.finalState_length_eq_total A hanchor hτ]
      exact i.isLt) = C.levelRecord A hanchor hτ i := by
  obtain ⟨⟨p, j⟩, rfl⟩ :=
    (OrderedGroupConcat.equiv (C.groupN A hanchor hτ)).surjective i
  change (C.finalState A hanchor hτ).entries[
    (OrderedGroupConcat.group (C.groupN A hanchor hτ) p j).val]'(by
      rw [C.finalState_length_eq_total A hanchor hτ]
      exact (OrderedGroupConcat.group (C.groupN A hanchor hτ) p j).isLt) =
      C.levelRecord A hanchor hτ
        (OrderedGroupConcat.group (C.groupN A hanchor hτ) p j)
  simpa only [OrderedGroupConcat.group_val, C.levelRecord_group A hanchor hτ p j] using
    C.finalState_get_groupRecord A hanchor hτ p j

/-- Legality remains relative to the exact full candidate prefix. -/
theorem levelRecord_legal
    (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    C.Legal ((C.finalState A hanchor hτ).entries.take i.val)
      (C.levelRecord A hanchor hτ i) := by
  have h := (C.finalState A hanchor hτ).legal_get i.val (by
    rw [C.finalState_length_eq_total A hanchor hτ]
    exact i.isLt)
  simpa only [C.finalState_get_levelRecord A hanchor hτ i] using h

theorem prefix_nextOrdinal
    (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    C.nextOrdinal ((C.finalState A hanchor hτ).entries.take i.val) =
      C.base + i.val := by
  unfold nextOrdinal
  rw [List.length_take, C.finalState_length_eq_total A hanchor hτ,
    Nat.min_eq_left i.isLt.le]

theorem prefix_nextBudget
    (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    C.nextBudget ((C.finalState A hanchor hτ).entries.take i.val) =
      candidateBudget (C.base + i.val) := by
  unfold nextBudget
  rw [C.prefix_nextOrdinal A hanchor hτ i]

/-- Detector and full proper-ancestor estimates for the actual stored record. -/
theorem levelRecord_spec
    (i : Fin (OrderedGroupConcat.total (C.groupN A hanchor hτ))) :
    ‖(C.levelRecord A hanchor hτ i).functional‖ ≤ 1 ∧
    (∀ z ∈ C.detectorSet ((C.finalState A hanchor hτ).entries.take i.val),
      1 - candidateBudget (C.base + i.val) ≤
        (C.levelRecord A hanchor hτ i).functional
          (((C.levelRecord A hanchor hτ i).map C.anchor : X) - z)) ∧
    (∑ j : Fin (C.candidateAncestors (C.levelRecord A hanchor hτ i).parent).length,
      ‖(C.candidateAncestorMap (C.levelRecord A hanchor hτ i).parent j
          ((C.levelRecord A hanchor hτ i).map C.anchor) : X) -
        ((C.levelRecord A hanchor hτ i).map C.anchor : X)‖) ≤
      candidateBudget (C.base + i.val) := by
  simpa only [Legal, C.prefix_nextBudget A hanchor hτ i] using
    C.levelRecord_legal A hanchor hτ i

end ReflexiveFixedPoints.CandidateContext

end

end OAI
