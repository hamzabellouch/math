import OAI.Analysis.MarkovType.JamesEnflo
import OAI.Analysis.MarkovType.PisierPowerRenorming

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasEquivalentUCNorm_iff_reflexive_finitelyRepresentable :
    HasEquivalentUCNorm X ↔
      ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y],
        FinitelyRepresentable Y X → CanonicallyReflexive Y := by
  constructor
  · intro h Y _ _ _ hYX
    exact h.canonicallyReflexive_of_finitelyRepresentable hYX
  · exact hasEquivalentUCNorm_of_reflexive_finitelyRepresentable

theorem hasEquivalentUCNorm_iff_hasEquivalentUSNorm [CompleteSpace X] :
    HasEquivalentUCNorm X ↔ HasEquivalentUSNorm X := by
  constructor
  · intro h
    obtain ⟨N, q, hq, hq₂, C, hC, hSym, hPower, hModulus, hUniform⟩ :=
      exists_power_smooth_equivalentNorm h
    exact ⟨N, hUniform⟩
  · exact hasEquivalentUCNorm_of_hasEquivalentUSNorm

end MarkovSuperreflexivity

end OAI
