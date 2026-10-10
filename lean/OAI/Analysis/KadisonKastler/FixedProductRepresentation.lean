import OAI.Analysis.KadisonKastler.FixedProductFactor
import OAI.Analysis.KadisonKastler.PublishedStandardRepresentation
import OAI.Analysis.KadisonKastler.NormalTypeIII1Transport
import OAI.Analysis.KadisonKastler.NormalFaithfulTensor
import OAI.Analysis.KadisonKastler.FaithfulTensorRange

namespace OAI

/-! # The fixed tensor factor in an arbitrary separable representation

Choose the faithful cyclic representation only to prove the factor's
type. Tensor functoriality and core independence transfer that conclusion
back to the user's original represented algebra.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

theorem TwoRatioProductModel.tensor_typeIII1_general
    (P : TwoRatioProductModel.{u})
    (hModular : PublishedModularSpectralResolution.{u})
    (hK : PublishedKaplanskyDensity.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (hClass : PublishedFactorialModularCore.{u})
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M) :
    TypeIII1Factor (spatialProductAlgebra M P.stages.algebra) := by
  let S := tensorCompatibleCyclicRepresentation M
  have hSP := P.tensor_typeIII1 hModular hK hSpectral hDiagonal hClass
    S.K S.algebra (hM.of_starAlgEquiv S.equiv) S.vector S.unit_vector S.cyclic S.separating
  obtain ⟨dS, _⟩ := (hModular S.K S.algebra S.vector S.cyclic S.separating).some
  obtain ⟨dD, _⟩ := (hModular P.K P.stages.algebra P.stages.vector
    P.stages.cyclic P.stages.separating).some
  have hc := denseRange_spatialProduct_vector S.algebra P.stages.algebra
    S.vector P.stages.vector S.cyclic P.stages.cyclic
  have hs := separating_spatialProduct_vector S.algebra P.stages.algebra
    S.vector P.stages.vector S.cyclic P.stages.cyclic dS dD
  obtain ⟨_, m⟩ := (hModular (SpatialHilbert S.K P.K)
    (spatialProductAlgebra S.algebra P.stages.algebra)
    (tensorVector P.stages.vector S.vector) hc hs).some
  have hn : ‖tensorVector P.stages.vector S.vector‖ = 1 := by
    rw [norm_tensorVector_apply, S.unit_vector, P.stages.unit_vector, mul_one]
  exact TypeIII1Factor.of_faithfulTensorRepresentation M P.stages.algebra hSP
    (tensorVector P.stages.vector S.vector) hn hc hs m

end

end KadisonKastler

end OAI
