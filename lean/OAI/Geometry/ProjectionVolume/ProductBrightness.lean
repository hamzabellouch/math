import OAI.Geometry.ProjectionVolume.ProductNormals
import OAI.Geometry.ProjectionVolume.ProductCoefficients
import OAI.Geometry.ProjectionVolume.ProductFacetAreaValues
import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem productFacet_brightness (a : ProductFacetIndex) (u : Euclidean 20) :
    brightness (productFacet a) u =
      |productVelocity u a| / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
  have hsqrt : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  cases a with
  | inl a =>
    cases a with
    | none =>
      have hn : ‖liftFirst (diagonalUnitNormal 10)‖ = 1 := by
        rw [liftFirst_norm]
        exact diagonalUnitNormal_norm 10 (by norm_num)
      rw [brightness_of_subset_affine_hyperplane u (liftFirst (diagonalUnitNormal 10))
        hn (Real.sqrt 10)⁻¹ _ productFacet_left_diagonal_plane]
      rw [show 20 - 1 = 19 by rfl, productFacet_inl_none_area,
        ENNReal.toReal_ofReal (by positivity), inner_liftFirst, inner_diagonalUnitNormal]
      simp only [productVelocity, simplexVelocity, abs_neg, abs_div, Nat.cast_ofNat,
        abs_of_pos hsqrt]
      field_simp
    | some i =>
      have hn : ‖liftFirst (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
        rw [liftFirst_norm, coordinate_normal_norm]
      rw [brightness_of_subset_affine_hyperplane u (liftFirst (EuclideanSpace.single i 1))
        hn 0 _ (productFacet_left_coordinate_plane i)]
      rw [show 20 - 1 = 19 by rfl, productFacet_inl_some_area,
        ENNReal.toReal_ofReal (by positivity)]
      simp [inner_liftFirst, EuclideanSpace.inner_single_right, productVelocity,
        simplexVelocity, div_eq_mul_inv]
  | inr a =>
    cases a with
    | none =>
      have hn : ‖liftSecond (diagonalUnitNormal 10)‖ = 1 := by
        rw [liftSecond_norm]
        exact diagonalUnitNormal_norm 10 (by norm_num)
      rw [brightness_of_subset_affine_hyperplane u (liftSecond (diagonalUnitNormal 10))
        hn (Real.sqrt 10)⁻¹ _ productFacet_right_diagonal_plane]
      rw [show 20 - 1 = 19 by rfl, productFacet_inr_none_area,
        ENNReal.toReal_ofReal (by positivity), inner_liftSecond, inner_diagonalUnitNormal]
      simp only [productVelocity, simplexVelocity, abs_neg, abs_div, Nat.cast_ofNat,
        abs_of_pos hsqrt]
      field_simp
    | some i =>
      have hn : ‖liftSecond (EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
        rw [liftSecond_norm, coordinate_normal_norm]
      rw [brightness_of_subset_affine_hyperplane u (liftSecond (EuclideanSpace.single i 1))
        hn 0 _ (productFacet_right_coordinate_plane i)]
      rw [show 20 - 1 = 19 by rfl, productFacet_inr_some_area,
        ENNReal.toReal_ofReal (by positivity)]
      simp [inner_liftSecond, EuclideanSpace.inner_single_right, productVelocity,
        simplexVelocity, div_eq_mul_inv]

theorem productWitness_brightness (u : Euclidean 20) :
    brightness productWitness u =
      ((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i| +
        (∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) /
          (2 * (Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
  by_cases hu : u = 0
  · simp [hu, brightness, firstBlock, secondBlock]
  calc
    brightness productWitness u =
        ∑ a : {a : ProductFacetIndex // productVelocity u a < 0},
          brightness (productFacet a.val) u := by
      rw [brightness_product_eq_front_sum u hu, Finset.mul_sum]
      rfl
    _ = ∑ a : {a : ProductFacetIndex // productVelocity u a < 0},
          -productVelocity u a.val / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [productFacet_brightness, abs_of_neg a.property]
    _ = (∑ a : {a : ProductFacetIndex // productVelocity u a < 0},
          -productVelocity u a.val) / ((Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
      rw [Finset.sum_div]
    _ = ((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i| +
        (∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) /
          (2 * (Nat.factorial 9 : ℝ) * (Nat.factorial 10 : ℝ)) := by
      rw [product_front_coefficient]
      ring

end Paper092

end

end OAI
