import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CleanCellChartTargetBridge

namespace OAI

/-!
# Uniform rectifiability from restart surface pieces

`HasUniformRestartSurfacePieces` uniformly bounds the number and Lipschitz
constants of pieces covering restart models up to a prescribed weighted area
loss. Combining this data with AD regularity and the Riesz bound gives clean-cell
charts with half-mass deficit, and hence uniform rectifiability.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def HasUniformRestartSurfacePieces {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (G ε : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (P : ℝ≥0),
    ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      let Bad := fun i : SupportCellDescendant μ R hR k z =>
        ε ≤ bilateralBeta n μ i.center (1024 * i.radius)
      ∃ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
        (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
          ¬ Bad q.val → SelectedRestartSurfaceData n Bad q.val (E q) ε N P),
        ∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
              ENNReal.ofReal δ * μ q.val.cell

theorem uniformlyRectifiable_of_Riesz_and_uniform_restart_surface_pieces
    {p d : ℕ} (hnd : p + 1 ≤ d) (μ : Measure (Ambient d)) [μ.Regular]
    (hAD : ADRegular (p + 1) μ) (hRiesz : RieszL2Bounded (p + 1) μ)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth (p + 1) G μ)
    (ε : ℝ) (hε : 0 < ε) (hεfine : ε ≤ 1 / 281474976710656)
    (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hpieces : HasUniformRestartSurfacePieces (p + 1) μ G ε) :
    UniformlyRectifiable (p + 1) μ := by
  obtain ⟨δ, hδ, b, _, hcharts⟩ := original_AD_Riesz_recursive_chart_from_surface_pieces
    hnd μ hAD hRiesz G hG hg 1024 ε (by norm_num) hε hεfine hsmall (1 / 2) (by norm_num)
  obtain ⟨N, P, hdata⟩ := hpieces δ hδ
  apply uniformlyRectifiable_of_uniform_clean_cell_deficits μ hAD G hG hg
    (1 / 2) (by norm_num) (by norm_num)
    (badBudgetChartConstant (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) b)
  intro R hR k z hcore
  obtain ⟨E, data, hloss⟩ := hdata R hR k z hcore
  obtain ⟨g, hg, _, hdeficit⟩ := hcharts N P R hR k z hcore E data hloss
  exact ⟨g, hg, hdeficit⟩

end

end RieszRectifiability

end OAI
