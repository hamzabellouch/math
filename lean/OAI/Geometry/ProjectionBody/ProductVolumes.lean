import OAI.Geometry.ProjectionBody.SimplexVolume
import OAI.Geometry.ProjectionBody.ProductFacetCharts

namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

theorem volume_productBody :
    volume productBody = ENNReal.ofReal (1 / ((Nat.factorial 10 : ℝ) * Nat.factorial 10)) := by
  simpa only [productBody, simplex_eq_coordinates, firstBlock, secondBlock,
    Set.mem_ofPred_eq, WithLp.ofLp_toLp] using
    volume_euclideanSimplexProduct 10 10

theorem volume_productFacetDomain (b : Bool) :
    volume (productFacetDomain b) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by
  cases b
  · simpa only [productFacetDomain, simplex_eq_coordinates, Set.preimage,
      Set.mem_prod, Set.mem_ofPred_eq, DiagonalZonotope.finAddEquivProd_apply,
      WithLp.ofLp_toLp] using
      volume_euclideanSimplexProduct 9 10
  · simpa only [productFacetDomain, simplex_eq_coordinates, Set.preimage,
      Set.mem_prod, Set.mem_ofPred_eq, DiagonalZonotope.finAddEquivProd_apply, WithLp.ofLp_toLp,
      mul_comm] using
      volume_euclideanSimplexProduct 10 9

theorem productFacetDomain_compact (b : Bool) : IsCompact (productFacetDomain b) := by
  cases b
  · exact (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).toHomeomorph.isCompact_preimage.mpr
      ((simplex_compact 9).prod (simplex_compact 10))
  · exact (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).toHomeomorph.isCompact_preimage.mpr
      ((simplex_compact 10).prod (simplex_compact 9))

end ProjectionCounterexample

end

end OAI
