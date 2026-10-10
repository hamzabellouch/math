import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

namespace Invariant233.ProductPhases

open scoped BigOperators

def consecutiveBlock (m : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  Finset.Ico (∑ r ∈ Finset.range j, m r)
    ((∑ r ∈ Finset.range j, m r) + m j)

end Invariant233.ProductPhases

end OAI
