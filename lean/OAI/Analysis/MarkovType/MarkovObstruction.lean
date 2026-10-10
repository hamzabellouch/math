import OAI.Analysis.MarkovType.FiniteWalk
import OAI.Analysis.MarkovType.ForwardBound
import OAI.Analysis.MarkovType.PowerGrowth

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem MarkovTypeWith.not_coordinatesRepresentable {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hp : 1 < p) (N : OrderedNorm) :
    ¬ CoordinatesRepresentable X N := by
  intro hNX
  apply not_all_walk_moment_bounds (K := K) hp
  intro n hn
  obtain ⟨W⟩ := finiteWalk N n (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact W.markov_moment_bound hn hX hNX

end MarkovSuperreflexivity

end

end OAI
