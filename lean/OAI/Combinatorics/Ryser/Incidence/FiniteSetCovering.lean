import Mathlib.Combinatorics.Additive.RuzsaCovering

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Tactic.NormNum

namespace OAI

namespace RyserCoveringCounterexample.Incidence.FiniteSetEstimates

open scoped Pointwise

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

theorem covering_add (A B : Finset F) (hB : B.Nonempty) {K : ℝ}
    (hK : ((A + B).card : ℝ) ≤ K * (B.card : ℝ)) :
    ∃ T ⊆ A, (T.card : ℝ) ≤ K ∧ A ⊆ T + (B - B) := by
  exact Finset.ruzsa_covering_add hB hK

end RyserCoveringCounterexample.Incidence.FiniteSetEstimates

end OAI
