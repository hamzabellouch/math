import OAI.Analysis.Pureness.GroupAlgebra.CanonicalCauchyFreeGroupExactness
import OAI.Analysis.Pureness.States.RegularizedStateCauchyEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y)

abbrev regularizedStateCauchyPositive :=
  finiteSpectralPositiveQuasitrace
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f)
    (regularizedState_dimension_finite hsimple y hy f) 1

abbrev regularizedStateCauchyTriangle :=
  finiteSpectralPositiveQuasitrace_metricSize_add
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f)
    (regularizedState_dimension_finite hsimple y hy f) 1

lemma regularizedStateCauchyPositive_quotient :
    (regularizedStateCauchyPositive hsimple y hy f).CauchyQuotient
      (regularizedStateCauchyTriangle hsimple y hy f) =
        RegularizedStateCauchyQuotient hsimple y hy f 0 := rfl

theorem regularizedStateFreeGroupTensor_kernel
    (x : (regularizedStateCauchyPositive hsimple y hy f).CauchyFreeGroupTensorSource
      (regularizedStateCauchyTriangle hsimple y hy f)) :
    (regularizedStateCauchyPositive hsimple y hy f).canonicalCauchyFreeGroupTensorMap
      (regularizedStateCauchyTriangle hsimple y hy f) x = 0 ↔
      x ∈ (spatialTensorKernelIdeal
        (H := FaithfulHilbertSpace ((regularizedStateCauchyPositive hsimple y hy f).cauchySequenceAlgebra
          (regularizedStateCauchyTriangle hsimple y hy f)))
        (K := GroupL2 (FreeGroup ℕ))
        ((regularizedStateCauchyPositive hsimple y hy f).cauchyQuotientStarHom
          (regularizedStateCauchyTriangle hsimple y hy f))
        ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS
          (regularizedStateCauchyTriangle hsimple y hy f))
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal :=
  (regularizedStateCauchyPositive hsimple y hy f).canonicalCauchyFreeGroupTensorMap_zero_iff
    (regularizedStateCauchyTriangle hsimple y hy f) x
end CuntzPureness

end

end OAI
