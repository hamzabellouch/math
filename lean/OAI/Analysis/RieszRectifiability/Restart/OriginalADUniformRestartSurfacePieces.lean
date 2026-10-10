import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.OriginalADUniformSurfaceBallCharts
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartBallChartData
import OAI.Analysis.RieszRectifiability.Surfaces.RieszFromUniformSurfacePieces

namespace OAI

/-!
# Uniform surface pieces at restart roots

Uniform surface ball charts for an AD-regular measure furnish selected surface
data at every bad-beta restart root. The flatness threshold is fixed before the
loss tolerance, and the chart Lipschitz bound is shared across all roots. Core
admissibility passes to descendants, allowing the local chart's weighted
Hausdorff-measure loss estimate to supply `HasUniformRestartSurfacePieces`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_original_AD_uniform_restart_surface_pieces {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      HasUniformRestartSurfacePieces n μ G ε := by
  classical
  obtain ⟨ε, hε, hεfine, hsmall, hcharts⟩ := exists_original_AD_uniform_surface_ball_charts hn hnd μ hAD G hG hg
  refine ⟨ε, hε, hεfine, hsmall, ?_⟩
  intro δ hδ
  obtain ⟨M, hM⟩ := hcharts δ hδ
  refine ⟨1, M, ?_⟩
  intro R hR k z hcore
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta n μ i.center (1024 * i.radius)
  let Q := {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}
  have hlocal (q : Q) :
      ∃ (S : SupportCellDescendant μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩ →
          AffineSubspace ℝ (Ambient d)) (hS : ∀ i, IsAffineNPlane n (S i)),
        (∀ i, activeRegionCell (relativeRestartGood Bad q.val) i →
          bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
        ∃ f : S (supportCellRoot μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩) → Ambient d,
          IsActiveRegionLimitModel μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
            (relativeRestartGood Bad q.val) S hS ε f ∧
          ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
            LipschitzWith M g ∧ Set.range g ⊆ closedBall q.val.center (3 * q.val.radius) ∧
            (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
              (μH[(n : ℝ)] : Measure (Ambient d))
                ((Set.range f ∩ closedBall q.val.center (3 * q.val.radius)) \ Set.range g) ≤
                  ENNReal.ofReal δ * μ q.val.cell := by
    have hqcore : AdmissibleRadius μ (latticeRadius R (k + q.val.depth) / 8) := by
      simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using! q.val.core_admissible hcore
    obtain ⟨S, hS, hfit, f, hmodel, g, hglip, hgrange, hloss⟩ :=
      hM R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩ hqcore
    have hGood : relativeRestartGood Bad q.val =
        (fun i => bilateralBeta n μ i.center (1024 * i.radius) < ε) := relativeRestartGood_beta_eq ε q.val
    exact ⟨S, hS, by simpa only [hGood] using! hfit,
      f, by simpa only [hGood] using! hmodel, g, hglip, hgrange, hloss⟩
  choose S hS hfit f hmodel g hglip hgrange hloss using hlocal
  let E (q : Q) : Set (Ambient d) := Set.range (g q)
  let data (q : Q) : SelectedRestartSurfaceData n Bad q.val (E q) ε 1 M :=
    selectedRestartSurfaceDataOfBallChart Bad q.val (S q) (hS q) ε (hfit q)
      (f q) (hmodel q) (g q) M (hglip q) (hgrange q)
  refine ⟨E, (fun q _ => data q), ?_⟩
  intro q _hq
  change (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
    (μH[(n : ℝ)] : Measure (Ambient d))
      ((Set.range (f q) ∩ closedBall q.val.center (3 * q.val.radius)) \ Set.range (g q)) ≤
        ENNReal.ofReal δ * μ q.val.cell
  exact hloss q

end

end RieszRectifiability

end OAI
