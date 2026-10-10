import Mathlib
import OAI.Analysis.Commutator.CentralCorner
import OAI.Analysis.Commutator.UnitaryMainTransport

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)

lemma mem_center_algebra (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv a∈CentralCorner.center (algebra U M) ↔ a∈CentralCorner.center M := by
  rw [CentralCorner.mem_center,CentralCorner.mem_center,mem_algebra]
  constructor
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    intro b hb
    apply U.conjStarAlgEquiv.injective
    rw [map_mul,map_mul]
    exact hc _ ((mem_algebra U M b).mpr hb)
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    change U.conjStarAlgEquiv b*U.conjStarAlgEquiv a=U.conjStarAlgEquiv a*U.conjStarAlgEquiv b
    rw [←map_mul,←map_mul,hc b hb]

lemma center_range (Z : K →L[ℂ] K) (hZ : Z∈CentralCorner.center (algebra U M)) :
    ∃ T : H →L[ℂ] H,T∈CentralCorner.center M ∧ U.conjStarAlgEquiv T=Z := by
  obtain ⟨T,rfl⟩ := U.conjStarAlgEquiv.surjective Z
  exact ⟨T,(mem_center_algebra U M T).mp hZ,rfl⟩

end Kadison.UnitaryTransport

end

end
end

end OAI
