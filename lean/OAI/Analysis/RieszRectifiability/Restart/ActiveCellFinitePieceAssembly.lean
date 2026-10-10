import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellNormalizedAssembly
import OAI.Analysis.RieszRectifiability.Foundations.FinitePieceCoordinates

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeCellFinitePieceAssemblyConstant (d N : ℕ) (P M : ℝ≥0) : ℝ≥0 :=
  (lipschitzExtensionConstant (Ambient d) *
    separatedPatchGluingConstant (M * (4 * (32 * finitePartialCoordinateConstant d N P)))
      (32 * finitePartialCoordinateConstant d N P) (finitePartialCoordinateConstant d N P)) * 2

theorem exists_active_cell_chart_from_finite_pieces {n d : ℕ} (hn : 0 < n)
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
    (N : ℕ) (D : Fin N → Set (Ambient n))
    (hD : ∀ j, D j ⊆ ball (0 : Ambient n) q.radius)
    (piece : Fin N → Ambient n → Ambient d) (P : ℝ≥0)
    (hpieceLip : ∀ j, LipschitzOnWith P (piece j) (D j))
    (hpieceImage : ∀ j, piece j '' D j ⊆ closedBall q.center (3 * q.radius))
    (E : Set (Ambient d)) (hE : E = ⋃ j : Fin N, piece j '' D j)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith (activeCellFinitePieceAssemblyConstant d N P M) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      μ q.cell ≤ μ (q.cell ∩ Set.range g) +
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          μ (i.val.cell \ Set.range (child i)) := by
  obtain ⟨coord, hcoordBall, hcoord⟩ := exists_coordinates_of_finite_partial_charts hn N
    q.radius q.radius_pos q.center D hD piece P hpieceLip hpieceImage
  rw [← hE] at hcoordBall hcoord
  exact exists_active_cell_normalized_chart_with_mass_losses μ G hG hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel q hq E coord (finitePartialCoordinateConstant d N P)
    (finitePartialCoordinateConstant_ge_one d N P) hcoord hcoordBall child M hLip himage

end

end RieszRectifiability

end OAI
