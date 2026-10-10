import OAI.Analysis.KadisonKastler.FaithfulTensorRange
import OAI.Analysis.KadisonKastler.NormalTypeIII1Transport
import OAI.Analysis.KadisonKastler.SpatialSeparability

namespace OAI

/-! # The direct normal tensor equivalence for the faithful cyclic representation -/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem TypeIII1Factor.of_faithfulTensorRepresentation
    [TopologicalSpace.SeparableSpace K]
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (hN : TypeIII1Factor (spatialProductAlgebra (faithfulCyclicAlgebra M) D))
    (ξ : SpatialHilbert (faithfulCyclicSpace M) K) (hξ : ‖ξ‖ = 1)
    (hc : DenseRange (algebraVectorMap (spatialProductAlgebra (faithfulCyclicAlgebra M) D) ξ))
    (hs : Function.Injective
      (algebraVectorMap (spatialProductAlgebra (faithfulCyclicAlgebra M) D) ξ))
    (m : ModularSpectralResolution (spatialProductAlgebra (faithfulCyclicAlgebra M) D) ξ) :
    TypeIII1Factor (spatialProductAlgebra M D) := by
  exact hN.of_normalHom (M := spatialProductAlgebra M D)
    (faithfulTensorHom M D) (faithfulTensorHom_injective M D)
    (faithfulTensorHom_boundedWeakNormal M D) (faithfulTensorHom_mem M D)
    (faithfulTensorHom_generated_range M D) ξ hξ hc hs m

end

end KadisonKastler

end OAI
