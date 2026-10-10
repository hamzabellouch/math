import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments

namespace OAI

/-! # Exact finite-observable transports at word and law boundaries -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped Classical
noncomputable section

lemma SameLaw.word_length {a b : ℕ} (h : a=b) {Y Z : Type*} [Fintype Y]
    (f : List Bool → Z) (g : Y → Z)
    (hf : SameLaw (fun xs : Fin a → Bool => f (List.ofFn xs)) g) :
    SameLaw (fun xs : Fin b → Bool => f (List.ofFn xs)) g := by
  cases h
  exact hf

lemma SameLaw.of_mapLaw_eq {X Y Z : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] [Fintype Z] [DecidableEq Z]
    (f : X → Z) (g : Y → Z)
    (h : mapLaw (uniformLaw (α := X)) f=mapLaw (uniformLaw (α := Y)) g) :
    SameLaw f g := by
  intro phi
  rw [FiniteLawMoments.word_expectation,FiniteLawMoments.word_expectation,h]

end
end ContingencyTables.FiniteObservableTransport

end OAI
