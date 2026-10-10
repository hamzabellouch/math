import OAI.Analysis.KadisonKastler.PointedPowerProduct
import OAI.Analysis.KadisonKastler.PublishedTwoRatioProduct
import OAI.Analysis.KadisonKastler.TwoRatioStages
import OAI.Analysis.KadisonKastler.SpatialSeparability

namespace OAI

/-! # The concrete pointed product for the two fixed ratios

The constant matrix-state products are placed in the
two spatial tensor legs. Their finite moments, cyclicity and separation
give the exact two-family coordinate system used by the application.
Its finite stages include remote copies and finite complements.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- The two prescribed site families with their actual product-state representation. -/
def twoRatioPointedProduct : PointedMatrixProduct.{u} twoRatioSiteParameter := by
  let P := fixedPowersProduct.{u}
  let Q : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductMu) :=
    (constantPointedMatrixProduct fixedProductMu_pos fixedProductMu_lt_one).universeLift
  exact {
    K := SpatialHilbert P.K Q.K
    algebra := spatialProductAlgebra P.algebra Q.algebra
    vector := tensorVector Q.vector P.vector
    coordinates := P.coordinates.sum Q.coordinates }

/-- Increasing full matrix stages with the required remote-copy moments. -/
def twoRatioConcreteStages : ProductMatrixStages (H := twoRatioPointedProduct.{u}.K) :=
  twoRatioPointedProduct.coordinates.twoRatioStages

/-- The original site coordinates generate the constructed stage closure. -/
def twoRatioConcreteCoordinates : PointedMatrixSites twoRatioConcreteStages.{u}.algebra
    twoRatioConcreteStages.vector twoRatioSiteParameter :=
  twoRatioPointedProduct.coordinates.twoRatioStages_coordinates

end

end KadisonKastler

end OAI
