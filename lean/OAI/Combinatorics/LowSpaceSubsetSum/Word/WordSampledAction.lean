import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasured
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedExecution

namespace OAI

/-! # Sequential composition of measured seed generation and a stored action

The generated seed stays resident while the prepared action runs. Generation
work and action work are both charged, including the exhaustion branch.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSampledAction

open WordSeedRealization WordSeedMeasured

variable {w N : ℕ} {α : Type} [Fintype α] {S : SamplerCoupling α}

structure Result where
  answer : Bool
  work : ℕ
  cells : ℕ
  cursor : ℕ

def run {X : Realization w N S} (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) : Result :=
  let generated := E.run stream cursor
  match generated.accepted with
  | none => ⟨false,generated.work+1,max generated.cells 8,generated.cursor⟩
  | some accepted =>
      let out := action accepted.seed.val
      ⟨out.1.1,generated.work+out.1.2+1,
        max generated.cells (generated.retained+out.2+8),generated.cursor⟩

theorem value {X : Realization w N S} (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    (run E action stream cursor).answer =
      match (WordProgram.run stream X.program cursor).1 with
      | none => false | some s => (action s.val).1.1 := by
  have h := congrArg Prod.fst (E.value stream cursor)
  rw [←h]
  cases hg : (E.run stream cursor).accepted <;>
    simp only [run,hg,Option.map_none,Option.map_some]

theorem finite_value {X : Realization w N S} (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ) (words : Fin N → Fin (2^w)) :
    (run E action (WordProgram.finiteStream words) 0).answer =
      WordSeedRealization.execute X (fun s => (action s).1.1) false words :=
  value E action _ 0

theorem cursor_eq {X : Realization w N S} (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    (run E action stream cursor).cursor = (WordProgram.run stream X.program cursor).2 := by
  have h := congrArg Prod.snd (E.value stream cursor)
  rw [←h]
  cases hg : (E.run stream cursor).accepted <;> simp only [run,hg]

theorem cursor_le {X : Realization w N S} (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    (run E action stream cursor).cursor ≤ cursor+N := by
  rw [cursor_eq]
  exact (WordProgram.run_bound X.program N X.bounded stream cursor).2

theorem bounded {X : Realization w N S} (E : Execution X)
    (action : S.Seed → (Bool × ℕ) × ℕ) (W C R V D : ℕ)
    (hE : E.Bounded W C R) (hV : ∀ s, (action s).1.2 ≤ V)
    (hD : ∀ s, (action s).2 ≤ D)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    (run E action stream cursor).work ≤ W+V+1 ∧
      (run E action stream cursor).cells ≤ max C (R+D+8) := by
  have he := hE stream cursor
  cases ha : (E.run stream cursor).accepted with
  | none =>
    simp only [run,ha]
    exact ⟨by omega,max_le (he.2.1.trans (le_max_left _ _))
      ((show 8 ≤ R+D+8 by omega).trans (le_max_right _ _))⟩
  | some a =>
    simp only [run,ha]
    have hv := hV a.seed.val
    have hd := hD a.seed.val
    exact ⟨by omega,max_le_max he.2.1 (by omega)⟩

end LowSpaceSubsetSum.WordSampledAction

end

end OAI
