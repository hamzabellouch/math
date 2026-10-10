import OAI.Probability.MatroidSecretary.Secretary.PrefixObservationModel

/-!
# Online information model for the full-seed secretary consequence

The rule precommits its prefix length using only its complete initial seed.
Its current decision sees exactly that seed and the currently available ordered
label–weight history, with no sample vector and no future suffix permutation.
Observation-prefix arrivals are unconditionally rejected by the execution model.
-/
