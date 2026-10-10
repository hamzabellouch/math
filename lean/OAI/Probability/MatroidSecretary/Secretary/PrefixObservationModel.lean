import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet

open Finset

/-- The first `K` labels of a complete order, used only to specify the experiment. -/
def orderPrefix {n : ℕ} (π : ArrivalOrder n) (K : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun e => (π.symm e).val < K

/-- Labels visible in the observation prefix of the currently available history. -/
def prefixLabels {n : ℕ} {k : Fin n} (K : ℕ) (h : History n k) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin (k.val + 1) => j.val < K).image fun j => (h j).1

/-- The observed weights, extended by zero away from the observation prefix.
Repeated labels in malformed histories are summed; genuine histories have none. -/
noncomputable def prefixWeights {n : ℕ} {k : Fin n} (K : ℕ)
    (h : History n k) : Weights n :=
  fun e => ∑ j : Fin (k.val + 1), if j.val < K ∧ (h j).1 = e then (h j).2 else 0

end MatroidProphet

end OAI
