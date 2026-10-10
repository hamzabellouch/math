import Mathlib
import OAI.Analysis.Commutator.InfiniteCenter
import OAI.Analysis.Commutator.UnitaryCenterTransport

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.InfiniteAmplification

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma stable_center_range (M : VonNeumannAlgebra H) (U : Space ℕ H ≃ₗᵢ[ℂ] K)
    (Z : K →L[ℂ] K) (hZ : Z∈CentralCorner.center (UnitaryTransport.algebra U (algebra M))) :
    ∃ a : CentralCorner.center M,U.conjStarAlgEquiv (map a.val)=Z := by
  obtain ⟨T,hT,hTZ⟩ := UnitaryTransport.center_range U (algebra M) Z hZ
  obtain ⟨a,ha⟩ := center_range M T hT
  exact ⟨a,by rw [ha]; exact hTZ⟩

end Kadison.InfiniteAmplification

end

end
end

end OAI
