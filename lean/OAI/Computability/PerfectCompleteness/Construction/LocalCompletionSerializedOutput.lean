import OAI.Computability.PerfectCompleteness.Construction.LocalCompletionOutput
import OAI.Computability.PerfectCompleteness.Machines.LocalCompletionMachineLemmas

namespace OAI

section

namespace PerfectCompleteness.LocalCompletionSerializedOutput

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open LocalCompletionFamily
open scoped Classical

noncomputable section

variable {m l r q : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
  [∀ x, Fintype (L x)]
  (G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)
  (defaultL : ∀ x, L x) (hq : 0 < q)
  (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)

private theorem projection_eq_of_images {a b : ProjectionTable q}
    (h : a.images = b.images) : a = b := by
  cases a
  cases b
  cases h
  rfl

def entry (e : Fin m)
    (seed : Fin ((LocalCompletionGame.family G legalL legalR defaultL hq hsmall).size e)) :
    Edge l r q :=
  CompletionRounding.entries (LocalCompletionGame.family G legalL legalR defaultL hq hsmall)
    (CompletionRounding.enumeration
      (LocalCompletionGame.family G legalL legalR defaultL hq hsmall) ⟨e, seed⟩)

@[simp] theorem entry_left (e : Fin m)
    (seed : Fin ((LocalCompletionGame.family G legalL legalR defaultL hq hsmall).size e)) :
    (entry G legalL legalR defaultL hq hsmall e seed).left = G.left e := by
  simp only [entry, CompletionRounding.entries, Equiv.symm_apply_apply]

@[simp] theorem entry_right (e : Fin m)
    (seed : Fin ((LocalCompletionGame.family G legalL legalR defaultL hq hsmall).size e)) :
    (entry G legalL legalR defaultL hq hsmall e seed).right = G.right e := by
  simp only [entry, CompletionRounding.entries, Equiv.symm_apply_apply]

theorem entry_projection (e : Fin m)
    (seed : Fin ((LocalCompletionGame.family G legalL legalR defaultL hq hsmall).size e)) :
    (entry G legalL legalR defaultL hq hsmall e seed).projection =
      LocalCompletionSerialization.projection
        (LocalCompletionGame.result_correct G legalL legalR defaultL hq hsmall e) seed := by
  apply projection_eq_of_images
  let F := LocalCompletionGame.family G legalL legalR defaultL hq hsmall
  have h := congrArg (fun es : CompletionRounding.CompletedOccurrence F =>
      Vector.ofFn (F.map es.1 es.2))
    ((CompletionRounding.enumeration F).symm_apply_apply ⟨e, seed⟩)
  exact h

def local_machine_output (e : Fin m) :
    TM2OutputsInTime (LocalCompletionSerialization.computation hq).tm
      (LocalCompletionMachine.inputBits (LocalCompletionGame.input G legalL legalR defaultL e))
      (some (LocalCompletionSerialization.payloadBits
        (LocalCompletionGame.result G legalL legalR defaultL hq e))) 1 :=
  LocalCompletionSerialization.machine_output hq _

theorem local_machine_output_decodes (e : Fin m) :
    decodeWords (LocalCompletionSerialization.payloadBits
      (LocalCompletionGame.result G legalL legalR defaultL hq e)) >>=
        LocalCompletionSerialization.parsePayload q =
      some ((List.finRange
        ((LocalCompletionGame.family G legalL legalR defaultL hq hsmall).size e)).map
          (fun seed => (entry G legalL legalR defaultL hq hsmall e seed).projection)) := by
  rw [LocalCompletionSerialization.decode_payloadBits, Option.bind_eq_bind, Option.bind_some]
  rw [LocalCompletionSerialization.parse_payload
    (LocalCompletionGame.result_correct G legalL legalR defaultL hq hsmall e)]
  congr 1
  apply List.map_congr_left
  intro seed _
  exact (entry_projection G legalL legalR defaultL hq hsmall e seed).symm

end
end PerfectCompleteness.LocalCompletionSerializedOutput

end

end OAI
