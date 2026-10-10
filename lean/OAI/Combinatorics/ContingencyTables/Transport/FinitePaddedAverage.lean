import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordPadding
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments

namespace OAI

/-! # Observables of a padded and reindexed finite Boolean word -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS FirstSuccess ResidualMixture FiniteLawMoments
open scoped BigOperators Classical

noncomputable section

lemma padded_equiv_average {k N : ℕ} (hk : k ≤ N) {X : Type*} [Fintype X]
    (e : (Fin k → Bool) ≃ X) (f : X → ℝ) :
    uniformAverage (fun bits : Fin N → Bool => f (e (prefixWord hk bits)))=
      uniformAverage f := by
  have hp := word_expectation (prefixWord hk) (fun bits => f (e bits))
  rw [prefixWord_uniform,expectation_uniform] at hp
  exact hp.trans (uniformAverage_equiv e f)

end
end ContingencyTables.FairBits

end OAI
