import Mathlib.Data.List.OfFn
import OAI.Computability.PerfectCompleteness.Reduction.SignedCompletionSchedule

namespace OAI

section

namespace PerfectCompleteness.SignedScheduleIndex

open MetadataFreeSampler SignedCompletionSchedule
open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

def atIndex (signs : SignTuple branch n t) (i : Fin D) : Descriptor (rows := rows) (repeats := repeats) hq large :=
  ⟨signs, (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).get
    (Fin.cast (schedule_length (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).symm i)⟩

@[simp] theorem atIndex_signs (signs : SignTuple branch n t) (i : Fin D) :
    (atIndex hq large hn hbranch hrows signs i).1 = signs := rfl

private theorem ofFn_get_cast {β : Type*} {d : Nat} (xs : List β) (h : xs.length = d) :
    List.ofFn (fun i : Fin d => xs.get (Fin.cast h.symm i)) = xs := by
  have roundtrip := (List.ofFn_congr h xs.get).symm
  rw [List.ofFn_get] at roundtrip
  exact roundtrip

theorem ofFn_atIndex (signs : SignTuple branch n t) :
    List.ofFn (atIndex (repeats := repeats) hq large hn hbranch hrows signs) =
      (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).map (Sigma.mk signs) := by
  unfold atIndex
  rw [List.ofFn_comp', ofFn_get_cast
    (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs)
    (schedule_length (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs)]

theorem observations_eq {β : Type*} (signs : SignTuple branch n t)
    (observe : Descriptor (rows := rows) (repeats := repeats) hq large → β) :
    List.ofFn (fun i : Fin D => observe (atIndex hq large hn hbranch hrows signs i)) =
      (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).map (fun e => observe ⟨signs, e⟩) := by
  calc
    _ = (List.ofFn (atIndex hq large hn hbranch hrows signs)).map observe :=
      List.ofFn_comp' _ _
    _ = _ := by simp only [ofFn_atIndex, List.map_map, Function.comp_def]

theorem tables_eq (signs : SignTuple branch n t) :
    List.ofFn (fun i : Fin D =>
      descriptorTable hq large (atIndex hq large hn hbranch hrows signs i)) =
      (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).map
        (fun e => LocalCompletionFamily.table (result (rows := rows) (repeats := repeats) hq large signs e.1) e.2) :=
  observations_eq hq large hn hbranch hrows signs (descriptorTable hq large)

theorem acceptance_values_eq (signs : SignTuple branch n t)
    (accepts : Descriptor (rows := rows) (repeats := repeats) hq large → Bool) :
    List.ofFn (fun i : Fin D => accepts (atIndex hq large hn hbranch hrows signs i)) =
      (schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).map (fun e => accepts ⟨signs, e⟩) :=
  observations_eq hq large hn hbranch hrows signs accepts

theorem acceptance_list_eq (signs : SignTuple branch n t)
    (accepts : Descriptor (rows := rows) (repeats := repeats) hq large → Bool) :
    (List.ofFn (atIndex (repeats := repeats) hq large hn hbranch hrows signs)).filter accepts =
      ((schedule (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).filter
        (fun e => accepts ⟨signs, e⟩)).map (Sigma.mk signs) := by
  simp only [ofFn_atIndex, List.filter_map, Function.comp_def]

theorem acceptance (signs : SignTuple branch n t)
    (accepts : Descriptor (rows := rows) (repeats := repeats) hq large → Bool) :
    (((List.ofFn (atIndex hq large hn hbranch hrows signs)).filter accepts).length : ℝ) /
        D = (law (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs).probability (fun e => accepts ⟨signs, e⟩) := by
  have h := schedule_acceptance (rows := rows) (repeats := repeats) hq large hn hbranch hrows signs (fun e => accepts ⟨signs, e⟩)
  rw [schedule_length] at h
  simpa only [acceptance_list_eq, List.length_map] using h

def instruction {K Λ σ : Type} [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .load (fun state => save state (atIndex hq large hn hbranch hrows (selectSigns state) i))
    (.goto (fun _ => exit))

theorem instruction_pushBound {K Λ σ : Type} [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) :
    Runtime.statementPushBound
      (instruction (K := K) hq large hn hbranch hrows selectSigns save i exit) = 0 := rfl

theorem instruction_trace {K Λ σ : Type} [DecidableEq K] [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (instruction hq large hn hbranch hrows selectSigns save i exit) state tapes =
      ⟨some exit, save state (atIndex hq large hn hbranch hrows (selectSigns state) i), tapes⟩ :=
  rfl

theorem step {K Λ σ : Type} [DecidableEq K] [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (entry : Λ)
    (atEntry : program entry = instruction hq large hn hbranch hrows selectSigns save i exit)
    (state : σ) (tapes : K → List Bool) :
    TM2.step program ⟨some entry, state, tapes⟩ =
      some ⟨some exit, save state (atIndex hq large hn hbranch hrows (selectSigns state) i),
        tapes⟩ := by
  change some (TM2.stepAux (program entry) state tapes) = _
  rw [atEntry, instruction_trace]

def inTime {K Λ σ : Type} [DecidableEq K] [Finite σ]
    (selectSigns : σ → SignTuple branch n t) (save : σ → Descriptor (rows := rows) (repeats := repeats) hq large → σ)
    (i : Fin D) (exit : Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (entry : Λ)
    (atEntry : program entry = instruction hq large hn hbranch hrows selectSigns save i exit)
    (state : σ) (tapes : K → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some entry, state, tapes⟩
      (some ⟨some exit,
        save state (atIndex hq large hn hbranch hrows (selectSigns state) i), tapes⟩) 1 where
  steps := 1
  evals_in_steps := step hq large hn hbranch hrows selectSigns save i exit
    program entry atEntry state tapes
  steps_le_m := Nat.le_refl 1

end
end PerfectCompleteness.SignedScheduleIndex

end

end OAI
