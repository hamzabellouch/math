import OAI.Geometry.ProjectionVolume.ProductFacetAreas
import OAI.Geometry.ProjectionVolume.ProductFacetGeometry

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Paper092

theorem splitEuclideanProduct_ten_ten : splitEuclideanProduct 10 10 = splitBlocks := rfl

theorem productFacet_inl_some_area (i : Fin 10) :
    μHE[19] (productFacet (.inl (some i))) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inl_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_coordinate_facet_area_left 9 10 i]
  congr 1
  simp only [one_div, mul_inv_rev]
  ring

theorem productFacet_inr_some_area (i : Fin 10) :
    μHE[19] (productFacet (.inr (some i))) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inr_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_coordinate_facet_area_right 10 9 i]
  congr 1
  simp only [one_div, mul_inv_rev]

theorem productFacet_inl_none_area :
    μHE[19] (productFacet (.inl none)) =
      ENNReal.ofReal (Real.sqrt 10 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inl_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_diagonal_facet_area_left 9 10]
  congr 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  ring

theorem productFacet_inr_none_area :
    μHE[19] (productFacet (.inr none)) =
      ENNReal.ofReal (Real.sqrt 10 / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ))) := by
  rw [productFacet_inr_eq_preimage, ← splitEuclideanProduct_ten_ten]
  rw [simplexProduct_diagonal_facet_area_right 10 9]
  congr 1
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  ring

end Paper092

end

end OAI
