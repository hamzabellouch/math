import OAI.Analysis.KadisonKastler.StateBicentralizerCentralizer
import OAI.Analysis.KadisonKastler.SpatialSliceRecovery
import OAI.Analysis.KadisonKastler.SpatialProductState

namespace OAI

/-! # Bicentralizer reduction along the fixed product leg

The independent finite-site swaps give a trivial bicentralizer for the
product vector. In a tensor product the same exact centralizer tests
force every bicentralizer element into the first tensor leg. Triviality
of that leg is a separate hypothesis.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem ProductMatrixStages.bicentralizer_scalar (P : ProductMatrixStages (H := K))
    (a : Algebra P.algebra) (ha : stateBicentralizerMember P.vector a) :
    a=vectorFunctional P.vector a • 1 := by
  apply Subtype.ext
  apply P.state_centralizer_irreducible a.val a.property
  intro u hu hc
  have h := stateBicentralizerMember_commutes_of_productStateCentralizes P.vector ha
    (⟨u.val,hu⟩ : Algebra P.algebra) hc
  exact congrArg Subtype.val h.symm

theorem spatial_bicentralizer_mem_left (hK : PublishedKaplanskyDensity.{u})
    (M : VonNeumannAlgebra H) (P : ProductMatrixStages (H := K)) (ξ : H)
    (a : Algebra (spatialProductAlgebra M P.algebra))
    (ha : stateBicentralizerMember (tensorVector P.vector ξ) a) :
    ∃ b : Algebra M, a.val=spatialLeft (K := K) b.val := by
  obtain ⟨b,hb,he⟩ := spatial_relative_commutant_of_local_swaps M P.localSwaps
    P.unit_vector P.separating a.val a.property (by
      intro u hu hc
      let c : Algebra (spatialProductAlgebra M P.algebra) :=
        ⟨spatialRight u.val,spatialRight_mem_product M P.algebra hu⟩
      have hz := spatialRight_productStateCentralizes hK M P ξ u.val hc
      have hh := stateBicentralizerMember_commutes_of_productStateCentralizes
        (tensorVector P.vector ξ) ha c hz
      exact congrArg Subtype.val hh.symm)
  exact ⟨⟨b,hb⟩,he⟩

end

end KadisonKastler

end OAI
