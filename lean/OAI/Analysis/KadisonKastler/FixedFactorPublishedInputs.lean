import OAI.Analysis.KadisonKastler.ModularCoreStability
import OAI.Analysis.KadisonKastler.FixedProductRepresentation
import OAI.Analysis.KadisonKastler.PublishedExpectedMatrixSubfactor

namespace OAI

/-! # Published inputs for the fixed-factor preparation argument -/

namespace KadisonKastler

noncomputable section

universe u

/-- Every field refers to a separately documented published result.
There is no stability, preparation or fixed-factor conclusion among
these assumptions. -/
structure FixedFactorPublishedInputs : Prop extends ModularCorePublishedInputs.{u} where
  product : PublishedTwoRatioProduct.{u}
  pointed : PublishedPointedMatrixOperations.{u}
  modular : PublishedModularSpectralResolution.{u}
  coreClassification : PublishedFactorialModularCore.{u}
  kaplansky : PublishedKaplanskyDensity.{u}
  expected : PublishedExpectedMatrixSubfactor.{u}

theorem TwoRatioProductModel.typeIII1_of_published (P : TwoRatioProductModel.{u})
    (h : FixedFactorPublishedInputs.{u})
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M) :
    TypeIII1Factor (spatialProductAlgebra M P.stages.algebra) := by
  exact P.tensor_typeIII1_general
    h.modular h.kaplansky h.realSpectral h.diagonal h.coreClassification H M hM

end

end KadisonKastler

end OAI
