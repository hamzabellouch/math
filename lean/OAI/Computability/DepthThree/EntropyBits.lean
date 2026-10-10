import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

namespace OAI

namespace DepthThreeLowerBound

open scoped BigOperators

def trueCount {N : ℕ} (z : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => z i = true).card

theorem trueCount_le {N : ℕ} (z : Fin N → Bool) : trueCount z ≤ N := by
  simpa only [trueCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => z i = true))

theorem trueCount_cast {N : ℕ} (z : Fin N → Bool) :
    (trueCount z : ℝ) = ∑ i, if z i = true then (1 : ℝ) else 0 := by
  exact Finset.natCast_card_filter (fun i => z i = true) Finset.univ

end DepthThreeLowerBound

end OAI
