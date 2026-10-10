import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-!
# The published finite-chain Cheeger input

Levin and Peres, *Markov Chains and Mixing Times*, second edition (2017),
Theorem 13.10, equation (13.6), lower bound, together with the variational
characterization in Lemma 13.7. The theorem is attributed there to Sinclair
and Jerrum (1989) and Lawler and Sokal (1988).
Source: https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

The finite reversible lazy-chain Poincaré consequence is expressed using
stationary cut flow and the symmetric Dirichlet energy.
-/

namespace ContingencyTables.PublishedInputs

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable (X : Type*) [Fintype X]

/-- The smallest Cheeger consequence needed here. The cut inequality uses
unnormalized stationary flow across each cut once; `energy` includes the
usual factor one half in its symmetric pair-sum formula. -/
def FiniteCheeger : Prop :=
  ∀ (C : FiniteChain X) (κ : ℝ), 0 < κ →
    (∀ S : Finset X,
      κ * min (∑ x ∈ S, C.π x) (∑ x ∈ Sᶜ, C.π x) ≤
        ∑ x ∈ S, ∑ y ∈ Sᶜ, C.π x * C.P x y) →
    ∀ f : X → ℝ, C.variance f ≤ (2 / κ ^ 2) * C.energy f

end

end ContingencyTables.PublishedInputs

end OAI
