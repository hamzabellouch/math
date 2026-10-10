import OAI.Geometry.ProjectionVolume.ProductCounterexample
import OAI.Geometry.ProjectionVolume.SimplexValue

namespace OAI

namespace Paper092

theorem standardSimplex_normalizedProjectionVolume_lt_productWitness :
    normalizedProjectionVolume (standardSimplex 20) <
      normalizedProjectionVolume productWitness := by
  rw [standardSimplex_normalizedProjectionVolume 20 (by norm_num),
    productWitness_normalizedProjectionVolume]
  exact dimension_twenty_strict

end Paper092

end OAI
