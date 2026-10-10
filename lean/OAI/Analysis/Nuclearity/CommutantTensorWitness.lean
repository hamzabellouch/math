import OAI.Analysis.PureInfiniteness.FunctionalTensorRepresentation
import OAI.Analysis.Nuclearity.RepresentedTensorFunctional
import OAI.Analysis.Nuclearity.TensorFunctionalConjugation
import OAI.Analysis.WeakInfiniteness.CPSchwarz

namespace OAI

/-! A finite separating family is a single self-adjoint tensor test.
The representing data are constructed from the actual unitized GNS commutant. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace
open Complex selfAdjoint

namespace WeakPureInfiniteness

variable {B D I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D]
  [Fintype I] {l : I → selfAdjoint D →L[ℝ] ℝ}

namespace FunctionalTensorRepresentation

variable (R : FunctionalTensorRepresentation l)

def original : D →⋆ₙₐ[ℂ] (R.H →L[ℂ] R.H) :=
  R.π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)

omit [PartialOrder D] [StarOrderedRing D] [Fintype I] in
lemma original_commute (d : D) (c : R.C) : Commute (R.original d) (R.η c) :=
  R.commute (d : Unitization ℂ D) c

def tensorElement (x : I → selfAdjoint B) : MinimalTensor B R.C :=
  ∑ i, minimalElementary (x i : B) (R.c i)

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D] in
lemma tensorElement_selfAdjoint (x : I → selfAdjoint B) :
    IsSelfAdjoint (R.tensorElement x) :=
  minimalTensor_sum_selfAdjoint (fun i => (x i : B)) R.c
    (fun i => (x i).property) R.c_selfAdjoint

local instance representationOrder : PartialOrder R.C := CStarAlgebra.spectralOrder _
local instance representationOrdered : StarOrderedRing R.C := CStarAlgebra.spectralOrderedRing _
local instance tensorOrder : PartialOrder (MinimalTensor B R.C) := CStarAlgebra.spectralOrder _
local instance tensorOrdered : StarOrderedRing (MinimalTensor B R.C) := CStarAlgebra.spectralOrderedRing _

def tensorFunctional (hB : Nuclear B) (T : B →L[ℂ] D) (hT : CompletelyPositive T) :
    MinimalTensor B R.C →ₚ[ℂ] ℂ :=
  representedTensorFunctional hB R.original T hT R.η R.original_commute R.ξ

lemma tensorFunctional_element (hB : Nuclear B) (T : B →L[ℂ] D)
    (hT : CompletelyPositive T) (x : I → selfAdjoint B) :
    (R.tensorFunctional hB T hT (R.tensorElement x)).re =
      ∑ i, l i (realPart (T (x i))) := by
  rw [tensorFunctional, tensorElement, representedTensorFunctional_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : IsSelfAdjoint (T (x i)) := by
    change star (T (x i)) = T (x i)
    rw [← completelyPositive_map_star hT, (x i).property]
  have hr : realPart (T (x i)) = (⟨T (x i), hs⟩ : selfAdjoint D) := Subtype.ext hs.coe_realPart
  rw [hr]
  exact (R.represents i ⟨T (x i), hs⟩).symm

end FunctionalTensorRepresentation
end WeakPureInfiniteness

end

end OAI
