import Mathlib
import OAI.Analysis.WeakInfiniteness.QuantitativeSeparation
import OAI.Analysis.WeakInfiniteness.ScalingAssembly
import OAI.Analysis.WeakInfiniteness.UniverseIndividualInfiniteness

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exact_weaklyPurelyInfinite_stronglyPurelyInfinite_any
    (hA : Exact A) (hW : WeaklyPurelyInfinite A) : StronglyPurelyInfinite A := by
  have hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a) :=
    fun _ ha => exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any hA hW ha
  obtain ⟨σ,hσ,_,hsep⟩ := exists_quantitative_separatingPositives_any hA hpi
  apply stronglyPurelyInfinite_of_contractive
  intro a b ha hb han hbn ε hε
  exact contractive_spi_of_quantitative_separation hpi hσ hsep a b ha hb han hbn hε

end

end

end WeakPureInfiniteness
end

end OAI
