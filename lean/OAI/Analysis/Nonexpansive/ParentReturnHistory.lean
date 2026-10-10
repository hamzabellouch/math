import OAI.Analysis.Nonexpansive.CandidateSelection
import Mathlib.Data.List.OfFn

namespace OAI

/-!
# Exact chronological records of a finite parent return

The returned adaptive transitions append actual records. Their full list,
including records of coefficient zero, is recovered without changing the
prefix against which any detector was chosen.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

/-- A finite append sequence has its literal initial list followed by its records. -/
theorem append_run_prefix {R : Type*} {N : ℕ}
    (state : Fin (N + 1) → List R) (record : Fin N → R)
    (hstep : ∀ i : Fin N, state i.succ = state i.castSucc ++ [record i])
    (n : ℕ) (hn : n ≤ N) :
    state ⟨n, Nat.lt_succ_of_le hn⟩ =
      state ⟨0, Nat.succ_pos N⟩ ++
        List.ofFn (fun i : Fin n => record ⟨i, Nat.lt_of_lt_of_le i.isLt hn⟩) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hlt : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hle : n ≤ N := hlt.le
      rw [List.ofFn_succ', List.concat_eq_append, ← List.append_assoc]
      change state (Fin.succ ⟨n, hlt⟩) =
        (state ⟨0, Nat.succ_pos N⟩ ++
          List.ofFn (fun i : Fin n => record ⟨i, Nat.lt_of_lt_of_le i.isLt hle⟩)) ++
            [record ⟨n, hlt⟩]
      rw [hstep, Fin.castSucc_mk, ih hle]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace CandidateContext
namespace ParentReturn

variable {D : NormalizedMinimalData (X := X)} {C : CandidateContext D}
variable {p : Fin C.frontier.size} {initial : C.State} {τ : ℝ}
variable (R : C.ParentReturn p initial τ)

/-- The actual record appended by this adaptive step. -/
def record (i : Fin R.N) : CandidateRecord C :=
  Classical.choose ((R.legal i).2)

theorem record_parent (i : Fin R.N) : (R.record i).parent = p :=
  (Classical.choose_spec ((R.legal i).2)).1

theorem record_map (i : Fin R.N) : (R.record i).map = R.selected i :=
  (Classical.choose_spec ((R.legal i).2)).2.1

theorem record_legal (i : Fin R.N) :
    C.Legal (R.state i.castSucc).entries (R.record i) :=
  Classical.choose ((Classical.choose_spec ((R.legal i).2)).2.2)

/-- No previous record is rewritten by a transition. -/
theorem state_succ_entries (i : Fin R.N) :
    (R.state i.succ).entries =
      (R.state i.castSucc).entries ++ [R.record i] := by
  have hs := Classical.choose_spec ((Classical.choose_spec ((R.legal i).2)).2.2)
  rw [hs]
  rfl

/-- The selected prefix has exactly the state recorded at that time. -/
theorem state_entries (n : ℕ) (hn : n ≤ R.N) :
    (R.state ⟨n, Nat.lt_succ_of_le hn⟩).entries = initial.entries ++
      List.ofFn (fun i : Fin n => R.record ⟨i, Nat.lt_of_lt_of_le i.isLt hn⟩) := by
  have h := append_run_prefix (fun i => (R.state i).entries) R.record
    R.state_succ_entries n hn
  simpa only [R.start] using h

/-- Each candidate receives a fresh chronological position. -/
theorem state_length (n : ℕ) (hn : n ≤ R.N) :
    (R.state ⟨n, Nat.lt_succ_of_le hn⟩).entries.length =
      initial.entries.length + n := by
  rw [R.state_entries n hn]
  simp

/-- The full candidate group retains every record, including discarded ones. -/
def records : List (CandidateRecord C) := List.ofFn R.record

@[simp] theorem records_length : R.records.length = R.N := by
  simp [records]

def finalState : C.State := R.state ⟨R.N, Nat.lt_succ_self R.N⟩

theorem finalState_entries :
    R.finalState.entries = initial.entries ++ R.records := by
  exact R.state_entries R.N (Nat.le_refl R.N)

@[simp] theorem finalState_length :
    R.finalState.entries.length = initial.entries.length + R.N := by
  rw [R.finalState_entries, List.length_append, R.records_length]

/-- The exact stored record at its global position. -/
theorem finalState_get_record (i : Fin R.N) :
    R.finalState.entries[initial.entries.length + i.val]'(by
      rw [R.finalState_length]
      exact Nat.add_lt_add_left i.isLt _) = R.record i := by
  simp only [R.finalState_entries]
  rw [List.getElem_append_right (Nat.le_add_right _ _)]
  simp [records]

/-- Every record of this group belongs to the one parent being processed. -/
theorem records_parent (r : CandidateRecord C) (hr : r ∈ R.records) : r.parent = p := by
  have hmem : ∃ i, R.record i = r := by
    simpa only [records, List.mem_ofFn] using hr
  obtain ⟨i, rfl⟩ := hmem
  exact R.record_parent i

/-- An earlier state is exactly the corresponding prefix of the completed history. -/
theorem state_entries_eq_final_take (n : ℕ) (hn : n ≤ R.N) :
    (R.state ⟨n, Nat.lt_succ_of_le hn⟩).entries =
      R.finalState.entries.take (initial.entries.length + n) := by
  rw [R.state_entries n hn, R.finalState_entries]
  rw [List.take_length_add_append]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, records_length, Nat.min_eq_left hn]
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_take, records, List.getElem_ofFn]

end ParentReturn
end CandidateContext
end ReflexiveFixedPoints

end

end OAI
