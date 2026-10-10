import OAI.Geometry.RCD.Coordinates.RegularCenterRadialData
import OAI.Geometry.RCD.Coordinates.NearbyExactFrames

namespace OAI

/-! # Uniform comparisons between the actual neighboring radial frames -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The frames supplied by the common heat construction satisfy the
published overlap estimate at every admissible pair and dyadic scale. -/
theorem regular_pair_frame_bounds {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base first center : X} {a κ B J C A Cχ enlargement zeta eta Cg D Ca : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hfirst : first ∈ ball base (e.heat.radius / 32))
    (hcenter : center ∈ ball base (e.heat.radius / 32))
    (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
    (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center)
    (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (2 : ℝ) ^ n) * zeta) ≤ 1 / 3)
    (i : ℕ) (hroom : dist first center ≤ distanceSourceRadius e.heat.radius i / 4) :
    ‖(d1.frame i).symm.toContinuousLinearMap.comp (d2.frame i).toContinuousLinearMap‖ ≤ Real.sqrt 2 ∧
    ‖(d2.frame i).symm.toContinuousLinearMap.comp (d1.frame i).toContinuousLinearMap‖ ≤ Real.sqrt 2 := by
  have hs : 0 < distanceSourceRadius e.heat.radius i := distanceSourceRadius_pos e.heat.radius_pos i
  have hsR : distanceSourceRadius e.heat.radius i ≤ e.heat.radius := by
    have hh := distanceSourceRadius_outer_le e.heat.radius_pos.le i
    linarith
  exact nearby_exact_frames hX e.heat.coordinates first center hs hzeta hroom
    (d1.frame i) (d2.frame i) _ _ hsmall (d1.splitting i) (d2.splitting i)
    (d1.exactFrame i) (d2.exactFrame i)
    (e.volume first hfirst _ (by positivity) (by linarith))
    (e.volume center hcenter _ (by positivity) (by linarith))
    (e.volume center hcenter _ hs (by linarith))

end RegularPointCoordinates

end

end OAI
