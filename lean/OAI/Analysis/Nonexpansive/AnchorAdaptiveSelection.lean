import OAI.Analysis.Nonexpansive.Anchor
import OAI.Analysis.Nonexpansive.AdaptiveSelection

namespace OAI

/-!
# Adaptive selection for the constructed anchor

The analytic hypotheses of the generic finite-selection theorem are
discharged by the actual tail-limit set and closed-convex-hull conclusions
of `AnchorPoint`.  `resolventAnchorPoint` chooses that record from the
proved compact-semigroup construction for the actual resolvent tails.
-/

noncomputable section

open Set
open scoped BigOperators

namespace ReflexiveFixedPoints

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

/-- An anchor supports finite successive selections with arbitrary
state-dependent thresholds and post-map auxiliary choices. -/
theorem AnchorPoint.adaptive_selection
    [TopologicalSpace.MetrizableSpace (WeakCarrier K)]
    {H : ℕ → Set (K → K)} (A : AnchorPoint H)
    {S : Type v} (threshold : ℕ → S → ℕ)
    (hthreshold : ∀ i s, 1 ≤ threshold i s)
    (transition : ℕ → S → (K → K) → S → Prop) (initial : S)
    (htransition : ∀ i s G,
      G ∈ H (threshold i s) → ∃ s', transition i s G s')
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (N : ℕ), 0 < N ∧
      ∃ (state : Fin (N + 1) → S) (selected : Fin N → K → K)
        (β : Fin N → ℝ),
        state ⟨0, Nat.succ_pos N⟩ = initial ∧
        (∀ i : Fin N,
          selected i ∈ H (threshold i (state i.castSucc)) ∧
          transition i (state i.castSucc) (selected i) (state i.succ)) ∧
        (∀ i, 0 ≤ β i) ∧ (∑ i, β i = 1) ∧
        ‖(∑ i, β i • (selected i A.x : X)) - (A.x : X)‖ < τ := by
  exact adaptive_finite_selection (fun G => G A.x) H A.x A.D
    A.D_subset A.mem_closedConvexHull A.tail_closure threshold hthreshold
    transition initial htransition hτ

/-- The anchor is constructed from actual resolvent tails.  No idempotent,
return law, or tail-limit convex-hull statement is an extra premise. -/
def resolventAnchorPoint [CompleteSpace X]
    (hKnonempty : K.Nonempty) (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (hKweak : WeaklyCompact K) :
    AnchorPoint (tailFamily hKclosed hKconvex T hT) :=
  Classical.choice (exists_anchorPoint hKclosed hKconvex T hT hKnonempty hKweak)

end ReflexiveFixedPoints

end

end OAI
