import OAI.Combinatorics.ContingencyTables.Transport.StarReindex
import OAI.Combinatorics.ContingencyTables.Transport.CompletionStepApproximation
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits

namespace OAI

/-! # Reindexing the literal completion accept/reject decision -/

namespace ContingencyTables.CompletionTranslation
open FirstSuccess FairBits ResidualMixture
open scoped Classical

variable {X I J I' J' : Type*} [Fintype X] [DecidableEq X]
variable [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

omit [Fintype X] [DecidableEq X] in
theorem completionDecision_reindex
    (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none)
    (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x : X) (proposal : Option X) (A : Table (R x) (P x)) :
    completionDecision (fun x i => R x (eI i)) (fun x j => P x (eJ j)) x proposal
      (tableReindex eI eJ (R x) (P x) A)=completionDecision R P x proposal A := by
  cases proposal with
  | none => rfl
  | some y =>
    unfold completionDecision
    dsimp only
    have he := translated_nonnegative_reindex eI eJ hI hJ (R x) (R y) (P x) (P y) A
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (he.mp h₁))
    · exact False.elim (h₁ (he.mpr h₂))
    · rfl

theorem uniform_completionDecision_reindex
    (eI : Option I' ≃ Option I) (eJ : Option J' ≃ Option J)
    (hI : eI none=none) (hJ : eJ none=none)
    (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x : X) (proposal : Option X)
    [Nonempty (Table (R x) (P x))]
    [Nonempty (Table (fun i => R x (eI i)) (fun j => P x (eJ j)))] :
    mapLaw (uniformLaw (α := Table (fun i => R x (eI i)) (fun j => P x (eJ j))))
      (completionDecision (fun x i => R x (eI i)) (fun x j => P x (eJ j)) x proposal)=
    mapLaw (uniformLaw (α := Table (R x) (P x))) (completionDecision R P x proposal) := by
  rw [←uniform_equiv (tableReindex eI eJ (R x) (P x)),map_equiv]
  congr 1
  funext A
  exact completionDecision_reindex eI eJ hI hJ R P x proposal A

end ContingencyTables.CompletionTranslation

end OAI
