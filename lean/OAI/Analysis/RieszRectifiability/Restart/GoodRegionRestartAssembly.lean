import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.RestartChartStepBounds

namespace OAI

/-!
# Restart chart assembly in a good region

Immediate-child charts first assemble at selected stopping cells, then join the
finite pieces of the active region. The resulting ball chart covers both families;
its uncovered mass is bounded by the omitted surface area and child deficits.
The Lipschitz constant is controlled by two restart steps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def goodRegionRestartAssemblyConstant (d N : ℕ) (P M : ℝ≥0) : ℝ≥0 :=
  activeCellFinitePieceAssemblyConstant d N P (immediateChildAssemblyConstant d M)

theorem goodRegionRestartAssemblyConstant_le_two_steps (d N : ℕ) (P M : ℝ≥0) :
    goodRegionRestartAssemblyConstant d N P M ≤
      restartChartStepConstant d N P (restartChartStepConstant d N P M) := by
  have hgood := (restartChartStepConstant_bounds d N P (immediateChildAssemblyConstant d M)).2.2.2
  have hbad := (restartChartStepConstant_bounds d N P M).2.2.1
  exact hgood.trans (restartChartStepConstant_mono d N P hbad)

theorem exists_good_region_restart_chart {n d : ℕ} (hn : 0 < n)
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
      ∀ j : supportImmediateChildren μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩,
        ball (0 : Ambient n) j.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i j, LipschitzWith M (child i j))
    (himage : ∀ i j, Set.range (child i j) ⊆ closedBall j.val.center (2 * j.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith (goodRegionRestartAssemblyConstant d N P M) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g) ∧
      (∀ i j, j.val.cell ∩ Set.range (child i j) ⊆ Set.range g) ∧
      μ (q.cell \ Set.range g) ≤
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          ∑ j : supportImmediateChildren μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩,
            μ (j.val.cell \ Set.range (child i j)) := by
  classical
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hcharts (i : F) : ∃ h : ball (0 : Ambient n) i.val.radius → Ambient d,
      LipschitzWith (immediateChildAssemblyConstant d M) h ∧
      Set.range h ⊆ closedBall i.val.center (2 * i.val.radius) ∧
      (∀ j, j.val.cell ∩ Set.range (child i j) ⊆ Set.range h) ∧
      μ (i.val.cell \ Set.range h) ≤
        ∑ j : supportImmediateChildren μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩,
          μ (j.val.cell \ Set.range (child i j)) :=
    exists_immediate_child_chart_assembly hn μ R hR (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ (child i) M (hLip i) (himage i)
  choose stopped hstoppedLip hstoppedRange hstoppedCover hstoppedDeficit using hcharts
  obtain ⟨g, hgLip, hgRange, hparent, hstopCover, hdeficit⟩ :=
    exists_active_cell_finite_piece_deficit_assembly μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel hn q hq N D hD piece P hpieceLip hpieceImage E hE
      stopped (immediateChildAssemblyConstant d M) hstoppedLip hstoppedRange
  refine ⟨g, hgLip, hgRange, hparent, ?_, ?_⟩
  · intro i j y hy
    exact hstopCover i ⟨j.val.cell_subset_top hy.1, hstoppedCover i j hy⟩
  · exact hdeficit.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum hstoppedDeficit))

end

end RieszRectifiability

end OAI
