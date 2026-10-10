import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartAssembly

namespace OAI

/-!
# Surface-area loss in selected restart charts

At a good restart root, the mass left outside a selected surface piece is bounded
by its discarded Hausdorff area. Applying this estimate at each selected root
turns an area-loss hypothesis into the uniform deficit required by the recursive
chart assembly; bad roots contribute an empty remainder.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-- A good restart root converts discarded model area into a bound for the remaining mass. -/
theorem selected_restart_remainder_mass_le_surface_loss {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) (E : Set (Ambient d))
    (ε : ℝ) (hε : 0 < ε) (hεfine : ε ≤ 1 / 281474976710656)
    (hsmall : activeProjectionError d ε ≤ 1 / 128) (N : ℕ) (P : ℝ≥0)
    (a : SelectedRestartSurfaceData n Bad q E ε N P) :
    μ (selectedRestartRemainder Bad q E) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range a.model ∩ closedBall q.center (3 * q.radius)) \ E) := by
  rw [selected_restart_remainder_of_good_root Bad q hq E]
  exact active_cell_remainder_mass_le_discarded_area μ G hG hg R hR (k + q.depth)
    ⟨q.center, q.mem_net⟩ (relativeRestartGood Bad q) a.planes a.isPlane
    ε hε hεfine hsmall a.fits a.model a.isModel
    (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)
    (relative_restart_root_active Bad q hq) E

/-- Uniformly small area losses yield a recursive Lipschitz chart with prescribed mass deficit.
The deficit threshold and restart budget are chosen before the surface-piece parameters. -/
theorem original_AD_Riesz_recursive_chart_from_surface_pieces {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (G : ℝ) (hG : 0 < G)
    (hg : GlobalUpperGrowth (p + 1) G μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧ ∀ (N : ℕ) (P : ℝ≥0)
      (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      let Bad := fun i : SupportCellDescendant μ R hR k z =>
        ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
      ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
        (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
          ¬ Bad q.val → SelectedRestartSurfaceData (p + 1) Bad q.val (E q) ε N P),
        (∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant (p + 1) G) *
          (μH[((p + 1 : ℕ) : ℝ)] : Measure (Ambient d))
            ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
              ENNReal.ofReal δ * μ q.val.cell) →
        ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
          LipschitzWith (badBudgetChartConstant
            (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) b) g ∧
          Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
          μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
            ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, b, hb, hcharts⟩ := original_AD_Riesz_selected_restart_uniform_deficit
    hnd μ hAD hRiesz H ε hH hε ζ hζ
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro N P R hR k z hcore
  dsimp only
  intro E data hloss
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
  have hassemble := has_selected_restart_assembly_of_surface_data (Nat.succ_pos p)
    G hG hg Bad E ε hε hεfine hsmall N P data
  apply hcharts R hR k z hcore E _ hassemble
  intro q
  by_cases hq : Bad q.val
  · rw [selected_restart_remainder_of_bad_root Bad q.val hq (E q), measure_empty]
    exact zero_le
  · exact (selected_restart_remainder_mass_le_surface_loss μ G hG hg R hR k z
      Bad q.val hq (E q) ε hε hεfine hsmall N P (data q hq)).trans (hloss q hq)

end

end RieszRectifiability

end OAI
