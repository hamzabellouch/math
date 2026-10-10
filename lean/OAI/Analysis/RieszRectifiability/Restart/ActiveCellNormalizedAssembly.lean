import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.BoundedNormalizedBallCharts
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellChildImageMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_active_cell_normalized_chart_with_mass_losses {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) (coord : Ambient d → Ambient n) (L : ℝ≥0) (hL : 1 ≤ L)
    (hcoord : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (L : ℝ) * dist (coord x) (coord y))
    (hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) q.radius)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith ((lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) * 2) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      μ q.cell ≤ μ (q.cell ∩ Set.range g) +
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          μ (i.val.cell \ Set.range (child i)) := by
  obtain ⟨g, hgLip, hmass⟩ := exists_active_cell_glued_chart_with_mass_losses μ G hG hg
    R hR k z Good S hS ε hε hεfine hsmall hfit f hmodel q hq E coord L hL
    hcoord hcoordBall child M hLip himage
  obtain ⟨g', hg'Lip, hg'Range, hcover⟩ := exists_bounded_normalized_ball_chart q.radius
    q.center (2 * q.radius) (by linarith [q.radius_pos]) g _ hgLip
  have hsub : q.cell ∩ Set.range g ⊆ q.cell ∩ Set.range g' := by
    intro y hy
    exact ⟨hy.1, hcover ⟨q.dist_center_of_mem y hy.1, hy.2⟩⟩
  exact ⟨g', hg'Lip, hg'Range,
    hmass.trans (add_le_add (add_le_add (measure_mono hsub) le_rfl) le_rfl)⟩

end

end RieszRectifiability

end OAI
