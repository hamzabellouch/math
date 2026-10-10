import OAI.Geometry.RCD.Coordinates.RegularCutoffJets
import OAI.Geometry.RCD.Coordinates.FrozenCutoffDerivatives

namespace OAI

/-! # First and second directional bounds for the actual patch cutoffs -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The one fixed Gevrey base controls both derivative orders needed by
the metric update. The source radius is the actual pinching scale. -/
theorem regular_cutoff_directional_bounds {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta0 : 0 ≤ zeta) (hzeta : zeta ≤ 1 / 64)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (psi : EuclideanGevreyCutoff n) (i : ℕ)
    {q y : X} (hq : q ∈ e.heat.patchRegion) (hy : y ∈ e.heat.patchNet i)
    (hactive : e.heat.values q ∈ tsupport (e.heat.patchCutoff psi.value i y))
    (xi : Euclidean n) :
    let L := psi.constant * 536870912
    let s := distanceSourceRadius e.heat.radius (e.heat.shift + i)
    |fderiv ℝ (e.heat.patchCutoff psi.value i y) (e.heat.values q) xi| ≤
        (L ^ 2 + 4 * L ^ 3) / s * ‖e.heat.frozenAt q i xi‖ ∧
    |diagonalSecond (e.heat.patchCutoff psi.value i y) (e.heat.values q) xi| ≤
        (L ^ 2 + 4 * L ^ 3) / s ^ 2 * ‖e.heat.frozenAt q i xi‖ ^ 2 := by
  intro L s
  have hcont := (regular_actual_patch_cover hX e hzeta psi i).cutoff_smooth y
  apply frozen_cutoff_first_second (e.heat.frozenAt q i)
    (e.heat.patchCutoff psi.value i y) (e.heat.values q) xi
    (distanceSourceRadius_pos e.heat.radius_pos _) (by
      have hc := psi.constant_ge_one
      dsimp only [L]
      positivity) (hcont.of_le (by simp)).contDiffAt
  exact regular_cutoff_normalized_jet hX e hzeta0 hzeta hsmall psi i hq hy hactive

end RegularPointCoordinates

end

end OAI
