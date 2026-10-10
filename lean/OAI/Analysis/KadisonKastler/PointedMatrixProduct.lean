import OAI.Analysis.KadisonKastler.SpatialProductCyclic
import OAI.Analysis.KadisonKastler.TwoRatioReindex

namespace OAI

/-! # Finite-site coordinates for pointed matrix products

The finite moments below identify the actual matrix-state product. They
do not include any assertion about factor type, centralizers or absorption.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A coordinate description of the product of two-dimensional matrix
states. Only distinct-site moments are needed: repeated entries at a
site are reduced by the matrix-unit identities. -/
structure PointedMatrixSites {I : Type*} (M : VonNeumannAlgebra H) (Ω : H) (ν : I → ℝ) where
  valid : ∀ i, 0 < ν i ∧ ν i < 1
  site : I → Generator.MatrixUnitSystem (Fin 2) (H →L[ℂ] H)
  commuting : ∀ i j, i ≠ j → ∀ a b c d,
    Commute ((site i).entry a b) ((site j).entry c d)
  generates : M = generatedVonNeumannAlgebra (⨆ i, (site i).algebra)
  unit_vector : ‖Ω‖ = 1
  cyclic : DenseRange (algebraVectorMap M Ω)
  separating : Function.Injective (algebraVectorMap M Ω)
  moments : ∀ (l : List I), l.Nodup → ∀ (r c : I → Fin 2),
    inner ℂ Ω (((l.map fun i => (site i).entry (r i) (c i)).prod) Ω) =
      (l.map fun i => if r i = c i then (twoSiteWeight (ν i) (r i) : ℂ) else 0).prod

/-- A concrete pointed matrix product in its faithful product-state
representation. This is construction data, not a classification. -/
structure PointedMatrixProduct {I : Type} (ν : I → ℝ) where
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [nontrivialK : Nontrivial K]
  [separableK : TopologicalSpace.SeparableSpace K]
  algebra : VonNeumannAlgebra K
  vector : K
  coordinates : PointedMatrixSites algebra vector ν

attribute [instance] PointedMatrixProduct.normedK PointedMatrixProduct.innerK
  PointedMatrixProduct.completeK PointedMatrixProduct.nontrivialK
  PointedMatrixProduct.separableK

end

end KadisonKastler

end OAI
