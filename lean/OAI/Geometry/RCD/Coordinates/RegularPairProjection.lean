import OAI.Geometry.RCD.Coordinates.RegularSharpSources

namespace OAI

/-! # The physical two-center projection size in the common coordinate map -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual normalized least-squares residual of the two replacements. -/
def regularPairProjectionSize {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base first center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
    (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center) (i : ℕ) : ℝ :=
  let s := distanceSourceRadius e.heat.radius i
  let uc := centeredColumn (hausdorff n X) hX.quadratic
    (transformedColumn (hausdorff n X) hX.quadratic e.heat.coordinates (d2.frame i))
    ((d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (e.heat.values center)) e.one.sobolev
  ‖normalizeLocalL2 (hausdorff n X) (ball center ((1 / 2048) * s))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (affineResidual (hausdorff n X) hX.quadratic
      (radiusScaledColumns (hausdorff n X) hX.quadratic s uc)
      (ball center ((1 / 2048) * s)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball center ((1 / 2048) * s))
        ((s ^ 2)⁻¹ • (d2.replacement.replacement i - d1.replacement.replacement i))))‖

end RegularPointCoordinates

end

end OAI
