import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! Completeness of the image of finite-dimensional real coordinates. -/

namespace DefocusingNLS

theorem finiteCoordinate_complete {H F : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (c : H →L[ℝ] F) : CompleteSpace c.range :=
  FiniteDimensional.complete ℝ c.range

end DefocusingNLS

end OAI
