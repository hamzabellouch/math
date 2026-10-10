import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

open scoped Pointwise

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance instStarModuleGenerated : StarModule ℂ (H →L[ℂ] H) :=
  ContinuousLinearMap.instStarModuleId

noncomputable def vonNeumannGenerated (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) :
        Set (H →L[ℂ] H))) = _
    rw [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]
    exact (StarSubalgebra.coe_centralizer_centralizer ℂ s).symm

end Invariant233

end OAI
