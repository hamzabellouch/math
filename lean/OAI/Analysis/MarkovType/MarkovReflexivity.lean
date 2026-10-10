import OAI.Analysis.MarkovType.OrderedNormConstruction
import OAI.Analysis.MarkovType.MarkovObstruction

namespace OAI

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem MarkovTypeWith.finitelyRepresentable_reflexive {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hp : 1 < p)
    (hYX : FinitelyRepresentable Y X) : CanonicallyReflexive Y := by
  classical
  by_contra hNR
  obtain ⟨N, hNX⟩ :=
    exists_orderedNorm_of_nonreflexive_finitelyRepresentable hNR hYX
  exact hX.not_coordinatesRepresentable hp N hNX

theorem HasNontrivialMarkovType.finitelyRepresentable_reflexive
    (hX : HasNontrivialMarkovType X) (hYX : FinitelyRepresentable Y X) :
    CanonicallyReflexive Y := by
  obtain ⟨p, hp, K, hK⟩ := hX
  exact hK.finitelyRepresentable_reflexive hp hYX

theorem HasMarkovType.two_finitelyRepresentable_reflexive
    (hX : HasMarkovType 2 X) (hYX : FinitelyRepresentable Y X) :
    CanonicallyReflexive Y := by
  obtain ⟨K, hK⟩ := hX
  exact hK.finitelyRepresentable_reflexive (by norm_num) hYX

end MarkovSuperreflexivity

end OAI
