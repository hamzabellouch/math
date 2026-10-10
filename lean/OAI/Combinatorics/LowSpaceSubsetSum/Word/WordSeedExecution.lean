import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedRealization
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRunLaw

namespace OAI

/-! # Running the prepared action on actual word-generated seeds -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedRealization

variable {w N : ℕ} {α β : Type} [Fintype α] {S : SamplerCoupling α}

def run (X : Realization w N S) (words : Fin N → Fin (2^w)) :=
  WordProgram.run (WordProgram.finiteStream words) X.program 0

theorem run_reads (X : Realization w N S) (words : Fin N → Fin (2^w)) :
    (run X words).2 ≤ N := by
  simpa only [run,Nat.zero_add] using
    (WordProgram.run_bound X.program N X.bounded (WordProgram.finiteStream words) 0).2

theorem run_probability (X : Realization w N S) (P : Option α → Prop) :
    (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability
      (fun words => P (observe S (run X words).1)) = S.boundedLaw.probability P := by
  unfold run
  exact (WordProgram.run_probability X.program N X.bounded
    (fun s => P (observe S s))).symm.trans
      ((WordProgram.probability_map (observe S) X.program P).symm.trans (X.faithful P))

def execute (X : Realization w N S) (action : S.Seed → β) (failure : β)
    (words : Fin N → Fin (2^w)) : β :=
  match (run X words).1 with
  | none => failure
  | some s => action s.val

/-- The action's value (which may itself contain its work counter) and
the separate number of fair words read. This does not charge continuations
as free machine operations. -/
def executeCounted (X : Realization w N S) (action : S.Seed → β) (failure : β)
    (words : Fin N → Fin (2^w)) : β × ℕ :=
  let out := run X words
  (match out.1 with | none => failure | some s => action s.val,out.2)

theorem executeCounted_value (X : Realization w N S) (action : S.Seed → β) (failure : β)
    (words : Fin N → Fin (2^w)) :
    (executeCounted X action failure words).1 = execute X action failure words := rfl

theorem executeCounted_reads (X : Realization w N S) (action : S.Seed → β) (failure : β)
    (words : Fin N → Fin (2^w)) : (executeCounted X action failure words).2 ≤ N :=
  run_reads X words

theorem execute_success (X : Realization w N S) (action : S.Seed → β) (failure : β)
    (words : Fin N → Fin (2^w)) (s : SuccessfulSeed S)
    (h : (run X words).1 = some s) : execute X action failure words = action s.val := by
  simp only [execute,h]

theorem probability_success (X : Realization w N S) (test : S.Seed → Bool)
    (P : α → Prop)
    (h : ∀ s a, S.bounded s = some a → P a → test s = true) :
    S.boundedLaw.probability (fun a => ∃ x, a = some x ∧ P x) ≤
      (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability
        (fun words => execute X test false words = true) := by
  rw [←run_probability X (fun a => ∃ x, a = some x ∧ P x)]
  apply FiniteLaw.probability_mono
  intro words hw
  cases hs : (run X words).1 with
  | none =>
    simp only [hs,observe,Option.bind_none,reduceCtorEq,false_and,exists_false] at hw
  | some s =>
    obtain ⟨a,ha,hpa⟩ := hw
    have hb : S.bounded s.val = some a := by
      simpa only [hs,observe,Option.bind_some] using ha
    exact (execute_success X test false words s hs).trans (h s.val a hb hpa)

end LowSpaceSubsetSum.WordSeedRealization

end

end OAI
