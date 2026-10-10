import OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem reducedComponent_dimension (X : Scheme.{0}) (C : irreducibleComponents X) :
    topologicalKrullDim (reducedComponent X C) = topologicalKrullDim (C.val : Set X) := by
  change topologicalKrullDim
    ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).support : Set X) = _
  have he : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).support : Set X) = C.val := by
    simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [he]

def componentIntegralCurve {X : Scheme.{0}} (C : irreducibleComponents X)
    (hd : topologicalKrullDim (reducedComponent X C) = 1) :
    NumericalAmpleness.IntegralCurve X where
  scheme := reducedComponent X C
  embedding := reducedComponentι X C
  closedImmersion := inferInstance
  integral := inferInstance
  dimension := hd

theorem exists_component_dimension_one (X : Scheme.{0})
    (hd : topologicalKrullDim X = 1) :
    ∃ C : irreducibleComponents X, topologicalKrullDim (reducedComponent X C) = 1 := by
  obtain ⟨Z,hZ⟩ := NumericalAmpleness.exists_irreducibleClosed_full_dimension X 1 hd
  have hZ' : topologicalKrullDim (Z : Set X) = 1 := by simpa using hZ
  obtain ⟨S,hS,hZS⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (Z : Set X) Z.isIrreducible
  let C : irreducibleComponents X := ⟨S,hS⟩
  refine ⟨C, ?_⟩
  rw [reducedComponent_dimension]
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le X C.val).trans hd.le
  · rw [← hZ']
    exact (Topology.IsEmbedding.inclusion hZS).isInducing.topologicalKrullDim_le

theorem component_dimension_one_or_zero {X : Scheme.{0}}
    (hd : topologicalKrullDim X ≤ 1) (C : irreducibleComponents X) :
    topologicalKrullDim (reducedComponent X C) = 1 ∨
      topologicalKrullDim (reducedComponent X C) ≤ 0 := by
  have hdim := (reducedComponentι X C).isEmbedding.isInducing.topologicalKrullDim_le.trans hd
  by_cases h : topologicalKrullDim (reducedComponent X C) = 1
  · exact Or.inl h
  · right
    change topologicalKrullDim (reducedComponent X C) ≤ ((0 : ℕ) : WithBot ℕ∞)
    rw [← ENat.WithBot.lt_add_one_iff]
    simpa using lt_of_le_of_ne hdim h

end
end PiExponent.CurveCycle

end OAI
