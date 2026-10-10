import OAI.Geometry.ProjectionVolume.ProductCounterexample
import OAI.Geometry.ProjectionVolume.SimplexAffine

namespace OAI

namespace Paper092

theorem simplex_normalizedProjectionVolume_lt_productWitness
    (s : Affine.Simplex ℝ (Euclidean 20) 20) :
    normalizedProjectionVolume (convexHull ℝ (Set.range s.points)) <
      normalizedProjectionVolume productWitness := by
  rw [simplex_normalizedProjectionVolume (by norm_num),
    productWitness_normalizedProjectionVolume]
  exact dimension_twenty_strict

end Paper092

end OAI
