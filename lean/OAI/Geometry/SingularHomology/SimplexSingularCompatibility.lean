import OAI.Geometry.SingularHomology.SimplexSingularRealization
import OAI.Geometry.SingularHomology.AffineSingularRealization

namespace OAI

noncomputable section

namespace Problem340.SimplexSingularRealization

theorem realize_eq_realizeInSimplex (k n : ℕ) :
    realize k n = AffineSingularRealization.realizeInSimplex k n := by
  apply SingularSubdivision.linearMap_ext
  intro v
  rw [realize_generator, AffineSingularRealization.realizeInSimplex_generator]
  rfl

end Problem340.SimplexSingularRealization

end

end OAI
