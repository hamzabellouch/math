import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.BallChartPartialMap
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartAssembly

namespace OAI

/-!
# Selected restart surface data from a ball chart

A Lipschitz ball chart supplies the single covering piece in selected restart
surface data, alongside the given fitted planes and active-region limit model.
The relative good-cell condition for beta stopping is also identified with the
strict bilateral-beta bound after composing descendants.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def selectedRestartSurfaceDataOfBallChart
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z)
    (S : SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ)
    (hfit : ∀ i, activeRegionCell (relativeRestartGood Bad q) i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
      (relativeRestartGood Bad q) S hS ε f)
    (g : ball (0 : Ambient n) q.radius → Ambient d) (M : ℝ≥0) (hg : LipschitzWith M g)
    (himage : Set.range g ⊆ closedBall q.center (3 * q.radius)) :
    SelectedRestartSurfaceData n Bad q (Set.range g) ε 1 M where
  planes := S
  isPlane := hS
  fits := hfit
  model := f
  isModel := hmodel
  domains := fun _ => ball (0 : Ambient n) q.radius
  domains_bounded := fun _ => Subset.rfl
  pieces := fun _ => ballChartPartialMap q.radius g
  pieces_lipschitz := fun _ => ballChartPartialMap_lipschitzOn q.radius g M hg
  pieces_bounded := fun _ => by
    rw [ballChartPartialMap_image]
    exact himage
  pieces_cover := by simp only [ballChartPartialMap_image, iUnion_const]

theorem relativeRestartGood_beta_eq (ε : ℝ)
    (q : SupportCellDescendant μ R hR k z) :
    relativeRestartGood (fun i => ε ≤ bilateralBeta n μ i.center (1024 * i.radius)) q =
      (fun i => bilateralBeta n μ i.center (1024 * i.radius) < ε) := by
  funext i
  apply propext
  change (¬ ε ≤ bilateralBeta n μ i.center (1024 * (q.compose i).radius)) ↔ _
  rw [q.compose_radius i]
  exact not_le

end

end RieszRectifiability

end OAI
