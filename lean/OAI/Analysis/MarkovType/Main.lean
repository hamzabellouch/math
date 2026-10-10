import OAI.Analysis.MarkovType.MarkovReflexivity
import OAI.Analysis.MarkovType.OrderedNormStructural
import OAI.Analysis.MarkovType.PisierPowerRenorming
import OAI.Analysis.MarkovType.SmoothRenormed

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem MarkovTypeWith.hasEquivalentUCNorm {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hp : 1 < p) : HasEquivalentUCNorm X := by
  classical
  by_contra hnot
  obtain ⟨N, hNX⟩ := orderedNorm_of_not_hasEquivalentUCNorm hnot
  exact hX.not_coordinatesRepresentable hp N hNX

theorem HasNontrivialMarkovType.hasEquivalentUCNorm
    (hX : HasNontrivialMarkovType X) : HasEquivalentUCNorm X := by
  obtain ⟨p, hp, K, hK⟩ := hX
  exact hK.hasEquivalentUCNorm hp

theorem HasMarkovType.two_hasEquivalentUCNorm (hX : HasMarkovType 2 X) :
    HasEquivalentUCNorm X := by
  obtain ⟨K, hK⟩ := hX
  exact hK.hasEquivalentUCNorm (by norm_num)

theorem HasEquivalentUCNorm.hasNontrivialMarkovType [CompleteSpace X]
    (hX : HasEquivalentUCNorm X) : HasNontrivialMarkovType X := by
  obtain ⟨N, q, hq, hq₂, C, hC, hSym, _, _, _⟩ :=
    exists_power_smooth_equivalentNorm hX
  exact hasNontrivialMarkovType_of_equivalent_symmetricPowerSmooth
    N hq hq₂ hC.le hSym

theorem hasNontrivialMarkovType_iff_hasEquivalentUCNorm [CompleteSpace X] :
    HasNontrivialMarkovType X ↔ HasEquivalentUCNorm X :=
  ⟨HasNontrivialMarkovType.hasEquivalentUCNorm,
    HasEquivalentUCNorm.hasNontrivialMarkovType⟩

end MarkovSuperreflexivity

end OAI
