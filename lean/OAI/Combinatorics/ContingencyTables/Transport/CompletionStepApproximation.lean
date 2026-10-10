import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletionCounts
import OAI.Combinatorics.ContingencyTables.Transport.RationalWalkApproximation

namespace OAI

/-! # Completion replacement in the actual proposal-and-translation step -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]

/-- A proposal is either a hold or a target state. The sampled completion
is discarded after its literal translated-nonnegativity test. -/
def completionDecision (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (x : X) (proposal : Option X) (a : Table (R x) (P x)) : X :=
  match proposal with
  | none => x
  | some y => if ∀ i j,0 ≤ (a.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j then y else x

def completionStepLaw (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (proposal : X → RationalLaw (Option X))
    (draw : (x : X) → RationalLaw (Table (R x) (P x))) (x : X) : RationalLaw X :=
  bindLaw (proposal x) (fun y => mapLaw (draw x) (completionDecision R P x y))

/-- From a common state only the completion draw changes. Mapping to the
accept/reject decision and averaging over the same proposal cannot enlarge TV. -/
theorem completionStep_variation (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (proposal : X → RationalLaw (Option X))
    (μ ν : (x : X) → RationalLaw (Table (R x) (P x))) (η : ℚ)
    (h : ∀ x,variation (μ x) (ν x) ≤ η) (x : X) :
    variation (completionStepLaw R P proposal μ x) (completionStepLaw R P proposal ν x) ≤ η := by
  have hv := variation_bind_uniform (proposal x) (proposal x)
    (fun y => mapLaw (μ x) (completionDecision R P x y))
    (fun y => mapLaw (ν x) (completionDecision R P x y)) η
    (fun y => (variation_map _ _ _).trans (h x))
  simpa only [completionStepLaw,variation,sub_self,abs_zero,Finset.sum_const_zero,zero_div,zero_add] using hv

/-- The transition draws and the final completion all use fresh bits. The
bound is uniform even though the state supplied to each draw is adaptive. -/
theorem completionWalk_terminal_variation (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (proposal : X → RationalLaw (Option X))
    (μ ν : (x : X) → RationalLaw (Table (R x) (P x)))
    (output : (x : X) → Table (R x) (P x) → Y) (η : ℚ)
    (h : ∀ x,variation (μ x) (ν x) ≤ η) (x : X) (n : ℕ) :
    variation
      (bindLaw (walkLaw (completionStepLaw R P proposal μ) x n) (fun z => mapLaw (μ z) (output z)))
      (bindLaw (walkLaw (completionStepLaw R P proposal ν) x n) (fun z => mapLaw (ν z) (output z))) ≤
        (n+1)*η :=
  walkLaw_terminal_variation _ _ _ _ η
    (completionStep_variation R P proposal μ ν η h)
    (fun z => (variation_map _ _ _).trans (h z)) x n

end
end ContingencyTables.CompletionTranslation

end OAI
