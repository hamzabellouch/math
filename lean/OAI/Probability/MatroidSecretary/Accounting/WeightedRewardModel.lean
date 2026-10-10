import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! A separate score vector evaluates the actual accepted labels without changing
the observations or decisions. In particular, rounded analysis scores need not
be substituted for the arriving weights. -/

namespace MatroidProphet

open scoped BigOperators

noncomputable def hiddenScore {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w score : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ hiddenAcceptedThrough A r w π n, score e

/-- The order minimum is taken separately for each complete seed. -/
noncomputable def hiddenWorstScore {n bits : ℕ} (A : HiddenRule n bits)
    (w score : Weights n) (r : Seed bits) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (hiddenScore A r w score)

end MatroidProphet

end OAI
