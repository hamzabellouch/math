import OAI.Geometry.ProjectionVolume.ProductProjection
import OAI.Geometry.ProjectionVolume.ProjectionCoefficients

namespace OAI

open scoped BigOperators

namespace Paper092

theorem productVelocity_sum (u : Euclidean 20) :
    ∑ a, productVelocity u a = 0 := by
  simp only [Fintype.sum_sum_type, productVelocity, simplexVelocity_sum, add_zero]

theorem product_front_coefficient (u : Euclidean 20) :
    (∑ a : {a : ProductFacetIndex // productVelocity u a < 0}, -productVelocity u a.val) =
      ((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i| +
        (∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) / 2 := by
  have h := twice_sum_negative_eq_sum_abs (productVelocity u) (productVelocity_sum u)
  have habs : (∑ a, |productVelocity u a|) =
      (|∑ i, firstBlock u i| + ∑ i, |firstBlock u i|) +
        (|∑ i, secondBlock u i| + ∑ i, |secondBlock u i|) := by
    simp only [Fintype.sum_sum_type, productVelocity, Fintype.sum_option, simplexVelocity, abs_neg]
  rw [habs] at h
  linarith

end Paper092

end OAI
